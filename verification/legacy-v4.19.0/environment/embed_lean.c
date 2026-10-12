/* Explicit-root command-line host for the UNMODIFIED official Lean 4.19 library.
 * Uses Lean.initSearchPath(root), lean_run_frontend (trust level 0),
 * lean_write_module and lean_ir_emit_c. No procfs access or syscall interposition.
 * Intended only for this host where automatic installation discovery fails.
 */
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
extern void lean_initialize(void);
extern lean_object *l_Lean_initSearchPath(lean_object *, lean_object *, lean_object *);
extern lean_object *lean_enable_initializer_execution(lean_object *);
extern lean_object *lean_run_frontend(lean_object *, lean_object *, lean_object *, lean_object *, uint32_t, lean_object *, uint8_t, lean_object *, lean_object *, lean_object *);
extern lean_object *lean_name_mk_string(lean_object *, lean_object *);
extern lean_object *lean_module_name_of_file(lean_object *, lean_object *, lean_object *);
extern lean_object *lean_print_imports(lean_object *, lean_object *, lean_object *);
extern lean_object *lean_write_module(lean_object *, lean_object *, lean_object *);
extern lean_object *lean_ir_emit_c(lean_object *, lean_object *);
extern lean_object *l_Lean_KVMap_setBool(lean_object *, lean_object *, uint8_t);
extern lean_object *l_Lean_KVMap_setNat(lean_object *, lean_object *, lean_object *);
extern lean_object *l_Lean_KVMap_setString(lean_object *, lean_object *, lean_object *);
static lean_object *unwrap(lean_object *r) {
 if (lean_io_result_is_error(r)) { lean_io_result_show_error(r); exit(1); }
 return lean_io_result_take_value(r);
}
static lean_object *some_string(const char *s) {
 if (!s) return lean_box(0);
 lean_object *o=lean_alloc_ctor(1,1,0); lean_ctor_set(o,0,lean_mk_string(s)); return o;
}
static lean_object *mk_name(const char *s) {
 lean_object *n=lean_box(0); char *copy=strdup(s),*save=NULL;
 for (char *p=strtok_r(copy,".",&save);p;p=strtok_r(NULL,".",&save)) n=lean_name_mk_string(n,lean_mk_string(p));
 free(copy); return n;
}
static void putfile(const char *path, const char *text) {
 FILE *f=fopen(path,"wb"); if(!f){perror(path);exit(2);} fputs(text,f); fclose(f);
}
int main(int argc, char **argv) {
 if (argc<2) { fprintf(stderr,"usage: embed_lean SYSROOT [LEAN OPTIONS] FILE\n"); return 2; }
 const char *sysroot=argv[1], *filename=NULL,*ofile=NULL,*cfile=NULL,*ifile=NULL,*root=NULL;
 int json=0,deps=0; unsigned workers=4;
 for(int i=2;i<argc;i++) {
  if(!strcmp(argv[i],"--version")||!strcmp(argv[i],"-v")){ puts("Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e9495688c1567e78c0e68dbb96942aa, Release; explicit-root embedding)");return 0;}
  if(!strcmp(argv[i],"--githash")||!strcmp(argv[i],"-g")){puts("6caaee842e9495688c1567e78c0e68dbb96942aa");return 0;}
  if(!strcmp(argv[i],"--short-version")||!strcmp(argv[i],"-V")){puts("4.19.0");return 0;}
  if(!strcmp(argv[i],"--print-prefix")){puts(sysroot);return 0;}
  if(!strcmp(argv[i],"--print-libdir")){printf("%s/lib/lean\n",sysroot);return 0;}
 }
 lean_initialize();
 lean_dec(unwrap(l_Lean_initSearchPath(lean_mk_string(sysroot),lean_box(0),lean_io_mk_world())));
 lean_dec(unwrap(lean_enable_initializer_execution(lean_io_mk_world())));
 lean_object *opts=lean_box(0);
 for(int i=2;i<argc;i++) {
  char *a=argv[i];
  if(!strcmp(a,"-o")&&i+1<argc) ofile=argv[++i];
  else if(!strcmp(a,"-c")&&i+1<argc) cfile=argv[++i];
  else if(!strcmp(a,"-i")&&i+1<argc) ifile=argv[++i];
  else if((!strcmp(a,"--root")||!strcmp(a,"-R"))&&i+1<argc) root=argv[++i];
  else if(!strncmp(a,"--root=",7)) root=a+7;
  else if(!strcmp(a,"--json")) json=1;
  else if(!strcmp(a,"--deps")) deps=1;
  else if(!strcmp(a,"-q")||!strcmp(a,"--quiet")) {}
  else if(!strncmp(a,"-D",2)) {
   char *copy=strdup(a+2),*eq=strchr(copy,'='); if(!eq){fprintf(stderr,"invalid option %s\n",a);return 2;} *eq++=0;
   lean_object *name=mk_name(copy);
   if(!strcmp(eq,"true")||!strcmp(eq,"false")) opts=l_Lean_KVMap_setBool(opts,name,!strcmp(eq,"true"));
   else if(strspn(eq,"0123456789")==strlen(eq)) opts=l_Lean_KVMap_setNat(opts,name,lean_unsigned_to_nat(strtoul(eq,NULL,10)));
   else opts=l_Lean_KVMap_setString(opts,name,lean_mk_string(eq));
   free(copy);
  }
  else if((!strcmp(a,"-j")||!strcmp(a,"--threads"))&&i+1<argc) workers=strtoul(argv[++i],NULL,10);
  else if(!strncmp(a,"-j",2)&&strlen(a)>2) workers=strtoul(a+2,NULL,10);
  else if(a[0]=='-'){fprintf(stderr,"unsupported embedded frontend option: %s\n",a);return 2;}
  else if(!filename) filename=a;
  else {fprintf(stderr,"multiple input files are unsupported\n");return 2;}
 }
 if(!filename){fprintf(stderr,"expected input file\n");return 2;}
 lean_io_mark_end_initialization();
 lean_init_task_manager_using(workers);
 FILE *f=fopen(filename,"rb"); if(!f){perror(filename);return 2;}
 fseek(f,0,SEEK_END); long n=ftell(f); rewind(f);
 char *buf=malloc(n+1); if(fread(buf,1,n,f)!=(size_t)n)return 2; buf[n]=0; fclose(f);
 if(deps) {lean_dec(unwrap(lean_print_imports(lean_mk_string(buf),some_string(filename),lean_io_mk_world())));return 0;}
 lean_object *modr=lean_module_name_of_file(lean_mk_string(filename),some_string(root),lean_io_mk_world());
 lean_object *mod;
 if(lean_io_result_is_error(modr)&&!ofile&&!cfile){lean_dec(modr);mod=mk_name("_stdin");}
 else mod=unwrap(modr);
 lean_inc(mod);
 lean_object *p=unwrap(lean_run_frontend(lean_mk_string(buf),opts,lean_mk_string(filename),mod,0,some_string(ifile),json,lean_mk_empty_array(),lean_mk_empty_array(),lean_io_mk_world()));
 int ok=lean_unbox(lean_ctor_get(p,1));
 lean_object *env=lean_ctor_get(p,0);
 if(ok&&ofile){lean_inc(env);lean_dec(unwrap(lean_write_module(env,lean_mk_string(ofile),lean_io_mk_world())));}
 if(ok&&cfile){
  lean_inc(env);lean_inc(mod);lean_object *r=lean_ir_emit_c(env,mod);
  if(lean_ptr_tag(r)==0){fprintf(stderr,"C generation failed: %s\n",lean_string_cstr(lean_ctor_get(r,0)));return 1;}
  putfile(cfile,lean_string_cstr(lean_ctor_get(r,0)));
 }
 fflush(stdout);fflush(stderr);
 return ok?0:1;
}

module

public import Solution

@[expose] public section

/-!
These commands inspect theorem statements and the transitive axiom dependencies
of the checked proof terms. No theorem is introduced by this audit file.
-/

#print ImprovedSidorenko.RGraph.IsEmbedding
#print ImprovedSidorenko.MainEmbeddingStatement
#print ImprovedSidorenko.TuranUpperBound
#print ImprovedSidorenko.MainDensityStatement
#print ImprovedSidorenko.BinomialTuranUpperBound

#check ImprovedSidorenko.main_embedding
#check ImprovedSidorenko.main_density
#check ImprovedSidorenko.main_binomial_density
#check ImprovedSidorenko.main_binomial_limit_bound

#print axioms ImprovedSidorenko.RGraph.failureProb_tower
#print axioms ImprovedSidorenko.RGraph.edgePotential_update
#print axioms ImprovedSidorenko.RGraph.cliquePotential_expected_increment
#print axioms ImprovedSidorenko.RGraph.cliqueChoices_card_bound_by_potential
#print axioms ImprovedSidorenko.RGraph.one_step_decreases
#print axioms ImprovedSidorenko.RGraph.exists_small_load_partial_map
#print axioms ImprovedSidorenko.LocalLemma.finite_local_lemma
#print axioms ImprovedSidorenko.LocalLemma.eventProb_local_lemma
#print axioms ImprovedSidorenko.RGraph.local_completion
#print axioms ImprovedSidorenko.noninjective_probability_le
#print axioms ImprovedSidorenko.RGraph.embedding_of_initial_potential
#print axioms ImprovedSidorenko.RGraph.cliqueKernel_empty_eq_density
#print axioms ImprovedSidorenko.paperConstant_pow
#print axioms ImprovedSidorenko.kernel_embedding_of_polynomial_bound
#print axioms ImprovedSidorenko.main_embedding
#print axioms ImprovedSidorenko.main_density
#print axioms ImprovedSidorenko.normalizationFactor_tendsto
#print axioms ImprovedSidorenko.main_binomial_density
#print axioms ImprovedSidorenko.main_binomial_limit_bound

#print ImprovedSidorenko.extremalNumber
#print ImprovedSidorenko.turanDensity
#print axioms ImprovedSidorenko.RGraph.exists_extremal
#print axioms ImprovedSidorenko.RGraph.delete_vertex_card_le
#print axioms ImprovedSidorenko.RGraph.sum_deleted_edge_counts
#print axioms ImprovedSidorenko.extremalDensity_succ_le
#print axioms ImprovedSidorenko.extremalDensity_tendsto
#print axioms ImprovedSidorenko.main_turan_density
#print axioms ImprovedSidorenko.Registry.embedding
#print axioms ImprovedSidorenko.Registry.limit_exists
#print axioms ImprovedSidorenko.Registry.main_theorem

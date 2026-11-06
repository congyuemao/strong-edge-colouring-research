import Se20Part.DegreeProfiles
import Se20Part.GirthDegree
import Se20Part.MaximumCut
import Se20Part.TightComponents
import Se20Part.Critical
import Se20Part.LocalInjection
import Se20Part.Transversal
import Se20Part.AuditExamples
import Se20Part.PathEndpointDegree
import Se20Part.CompactTriangles
import Se20Part.ComponentConditional
import Se20Part.PackingEqualityComponents
import Se20Part.High24Seven
import Se20Part.F01
import Se20Part.F09Endpoints
import Se20Part.ThirteenKernel
import Se20Part.CriticalSizeChecks
import Se20Part.CriticalEndpointDegree
import Se20Part.PetersenMinusHypothesis
import Se20Part.RouteReduction
import Se20Part.G05FiniteReduction
import Se20Part.PaletteHall
import Se20Part.MultipartiteFive
import Se20Part.PetersenExtension
import Se20Part.SmallComponentReduction
import Se20Part.TwoRepresentativeSizeChecks
import Se20Part.MatchingCutGluing
import Se20Part.SmallCutPalette
import Se20Part.CutBoundary
import Se20Part.CutMinimal
import Se20Part.CutConnectivity
import Se20Part.ExternalStars
import Se20Part.K33Palette
import Se20Part.PetersenSupport
import Se20Part.PetersenMinusKernel
import Se20Part.PetersenMinusSupport
import Se20Part.PetersenIncident
import Se20Part.GallaiLowBlocks
import Se20Part.CliqueSeparator

-- Hypotheses such as Brooks/Haxell/JoosNguyen are ordinary arguments.
-- Consequently their absence from #print axioms is not a proof of them.
#print axioms Se20Part.strongColourable_mono
#print axioms Se20Part.card_conflicts_le_twentyFour
#print axioms Se20Part.card_conflicts_triangle_le_twenty
#print axioms Se20Part.L2_degree_eq_twentyFour
#print axioms Se20Part.forest_L2_eliminates
#print axioms Se20Part.forest_L2_chordal
#print axioms Se20Part.induced_cycle_length_bound
#print axioms Se20Part.Partition.energy_update
#print axioms Se20Part.Partition.minimum_degreeIn_le
#print axioms Se20Part.Partition.exists_minimum
#print axioms Se20Part.Partition.minimum_ten_degree_le_two
#print axioms Se20Part.Partition.minimum_nine_degree_le_two
#print axioms Se20Part.Partition.minimum_update
#print axioms Se20Part.Partition.weightedEnergy_update
#print axioms Se20Part.Partition.weighted_minimum_slack_le
#print axioms Se20Part.Partition.exists_weighted_minimum
#print axioms Se20Part.Partition.lovasz_degree_bound
#print axioms Se20Part.Partition.lovasz_partition
#print axioms Se20Part.routeQ_degree_bound
#print axioms Se20Part.Partition.zeroClasses_bound
#print axioms Se20Part.Partition.zeroClasses_ten
#print axioms Se20Part.Partition.zeroClasses_nine_deficit
#print axioms Se20Part.Partition.zeroClasses_profiles
#print axioms Se20Part.Partition.zero_neighbour_degree_le_one
#print axioms Se20Part.Partition.two_step_conditions
#print axioms Se20Part.Partition.monochromatic_edge_reaches_other_class
#print axioms Se20Part.colourable_of_partition
#print axioms Se20Part.propertyQ_twenty
#print axioms Se20Part.brooksPalette_sum
#print axioms Se20Part.brooks_partition_twenty
#print axioms Se20Part.nine_classes_one_defect
#print axioms Se20Part.long_cycles_independent_transversal
#print axioms Se20Part.Packing.tau_le_rank_add_full
#print axioms Se20Part.Packing.eighteen_implies_nineteen
#print axioms Se20Part.pentagonDouble_twenty_edges
#print axioms Se20Part.componentEdges_disjoint
#print axioms Se20Part.componentEdges_separated
#print axioms Se20Part.packing18_implies19
#print axioms Se20Part.full_edge_eighteen_of_joos
#print axioms Se20Part.triangle_local_repair
#print axioms Se20Part.triangle_insertion
#print axioms Se20Part.triangle_edges_last
#print axioms Se20Part.triangle_reducibility
#print axioms Se20Part.critical21_no_triangle
#print axioms Se20Part.critical21_min_degree
#print axioms Se20Part.matching_conflicts_le_six
#print axioms Se20Part.matching_seven_colourable
#print axioms Se20Part.L2LocalMap
#print axioms Se20Part.strongColourable_pullback
#print axioms Se20Part.L2_complete
#print axioms Se20Part.complete_five_conflict_degree
#print axioms Se20Part.degree_potential_isolate_counterexample

-- Second pass: these include all cited hypotheses as ordinary arguments.
#print axioms Se20Part.exists_pathCycleOrder
#print axioms Se20Part.component_pathCycleOrder
#print axioms Se20Part.PathCycleOrder.colourable_iff
#print axioms Se20Part.PathCycleOrder.delete_vertex_colourable
#print axioms Se20Part.PathCycleOrder.odd_cycle_deletion_even
#print axioms Se20Part.Partition.exists_minimumTwo
#print axioms Se20Part.Partition.minimum_ten_components
#print axioms Se20Part.Partition.minimum_nine_components
#print axioms Se20Part.degreeTwo_residual_colourable
#print axioms Se20Part.Partition.residual_classes
#print axioms Se20Part.proposition_one_one
#print axioms Se20Part.bad_count_strict_decrease
#print axioms Se20Part.Partition.flip_creates_odd_component
#print axioms Se20Part.Partition.zero_class_even_path
#print axioms Se20Part.Partition.zero_class_neighbour_degree_one
#print axioms Se20Part.Partition.internal_zero_class_even_path
#print axioms Se20Part.bad_count_le_of_old_bad
#print axioms Se20Part.Partition.minimumTwo_update_of_bad
#print axioms Se20Part.Partition.exists_minimumThree
#print axioms Se20Part.Partition.typed_triangle_replacement
#print axioms Se20Part.compact_has_hub
#print axioms Se20Part.compact_has_pivot
#print axioms Se20Part.compact_zeroClasses_le_four
#print axioms Se20Part.no_compact_triangles_ten
#print axioms Se20Part.compact_pivot_deficit_nine
#print axioms Se20Part.Partition.exists_cliqueMinimumThree
#print axioms Se20Part.Partition.weighted_clique_hub_monotone
#print axioms Se20Part.Partition.exists_weightedComponentMinimumThree
#print axioms Se20Part.Partition.weighted_bad_count_update_le
#print axioms Se20Part.Partition.weighted_component_hub_monotone
#print axioms Se20Part.Partition.tight_count_bound
#print axioms Se20Part.Partition.weighted_component_bad_hub_zero
#print axioms Se20Part.no_matching_clique_three
#print axioms Se20Part.component_bad_clique_is_matching
#print axioms Se20Part.component_minimum_conditional_twenty
#print axioms Se20Part.packingRank_eq_zero_iff
#print axioms Se20Part.packingRank_le_one_iff
#print axioms Se20Part.edge_bound_remove_isolates
#print axioms Se20Part.tauG_univ
#print axioms Se20Part.full_edge_packing_eighteen
#print axioms Se20Part.packing_eighteen_rank_le_one
#print axioms Se20Part.nineCirculant_degree_four
#print axioms Se20Part.nineCirculant_eighteen_edges
#print axioms Se20Part.nineCirculant_conflict_complete
#print axioms Se20Part.nineCirculant_tight
#print axioms Se20Part.tight_component_subset_equality
#print axioms Se20Part.packingRank_union
#print axioms Se20Part.tauG_union
#print axioms Se20Part.packing_equality_union
#print axioms Se20Part.circulant_component_equality
#print axioms Se20Part.packing_equality_biUnion
#print axioms Se20Part.legacy_conflictGraph_eq
#print axioms Se20Part.ambient_packing_twenty
#print axioms Se20Part.fortyOne_edges_independent_triple
#print axioms Se20Part.rank_two_card_le_forty
#print axioms Se20Part.high24_clique_seven
#print axioms Se20Part.GirthClique.girth_clique_seven
#print axioms Se20Part.GirthClique.girth_degreeTwo_clique_five
#print axioms Se20Part.critical21_endpoint_degree
#print axioms Se20Part.CriticalSizeChecks.component_product_obstruction
#print axioms Se20Part.CriticalSizeChecks.triangle_parameter_range
#print axioms Se20Part.CriticalSizeChecks.nontrivial_block_obstruction
#print axioms Se20Part.CriticalSizeChecks.all_singletons_common_neighbour
#print axioms Se20Part.CriticalSizeChecks.factor_component_obstruction
#print axioms Se20Part.CriticalSizeChecks.five_bag_sizes
#print axioms Se20Part.petersenMinus_degrees
#print axioms Se20Part.petersenMinus_seventyFour_edges
#print axioms Se20Part.GirthFive.disjoint_two_paths_centres_of_clique
#print axioms Se20Part.GirthFive.no_five_edge_path_clique
#print axioms Se20Part.GirthFive.no_three_two_paths_clique
#print axioms Se20Part.GirthFive.path_edge_attachment
#print axioms Se20Part.GirthFive.path_edge_typeA_unique
#print axioms Se20Part.GirthFive.path_edge_typeB_unique
#print axioms Se20Part.GirthFive.two_typeB_not_conflicting
#print axioms Se20Part.GirthFive.two_typeA_outer_adj
#print axioms Se20Part.GirthFive.typeA_typeB_connection
#print axioms Se20Part.GirthFive.two_typeA_one_typeB_impossible
#print axioms Se20Part.GirthFive.no_path_three_edges_clique
#print axioms Se20Part.commonExtensions_independent
#print axioms Se20Part.thirteenKernel_triple_counts
#print axioms Se20Part.thirteenKernel_independent_card_le_three
#print axioms Se20Part.thirteenKernel_degrees
#print axioms Se20Part.thirteenKernel_triple_normal_form_of_type
#print axioms Se20Part.thirteenKernel_representatives_distinct

-- Third pass: exact component accounting and the complete Route Q reduction.
#print axioms Se20Part.Partition.exists_minimumFive
#print axioms Se20Part.Partition.minimumFive_relative
#print axioms Se20Part.Partition.typedTriangles_flip_count
#print axioms Se20Part.Partition.typedPairs_flip_count
#print axioms Se20Part.Partition.typedTriangles_flip_no_triangle_count
#print axioms Se20Part.Partition.two_flip_compact_replacement
#print axioms Se20Part.shared_triangle_bridge
#print axioms Se20Part.diffuse_zero_hub
#print axioms Se20Part.diffuse_hub_saturation
#print axioms Se20Part.compact_closures_le_four
#print axioms Se20Part.no_diffuse_triangles_ten
#print axioms Se20Part.route_minimum_no_triangles
#print axioms Se20Part.routeQ_reduction
#print axioms Se20Part.exists_routeQ_reduction
#print axioms Se20Part.strong_clique_twenty
#print axioms Se20Part.twenty_clique_closed
#print axioms Se20Part.twenty_clique_rigidity
#print axioms Se20Part.critical21_clique_nineteen
#print axioms Se20Part.exists_critical21
#print axioms Se20Part.critical21_no_abstract_obstruction
-- The three G05 finite checks below are theorem arguments, NOT proved checks.
#print axioms Se20Part.critical21_fortyTwo_of_finite_checks
#print axioms Se20Part.small_edge_set_twenty_of_finite_checks
#print axioms Se20Part.rank_two_twenty_of_finite_checks
#print axioms Se20Part.palette_equiv_of_no_rectangle
#print axioms Se20Part.palette_equiv_of_budgets
#print axioms Se20Part.palette_cut_three
#print axioms Se20Part.palette_cut_four
#print axioms Se20Part.palette_cut_five
#print axioms Se20Part.palette_special_four
#print axioms Se20Part.merge_partial_palette
#print axioms Se20Part.near_full_lists_sdr_or_uniform
#print axioms Se20Part.three_eight_lists_overlap
#print axioms Se20Part.small_colour_pool
#print axioms Se20Part.merge_three_parts
#print axioms Se20Part.paired_lists_hall
#print axioms Se20Part.three_parts_six_choosable
#print axioms Se20Part.four_parts_seven_choosable
#print axioms Se20Part.triple_pair_repair
#print axioms Se20Part.four_uniform_one_disjoint_hall
#print axioms Se20Part.five_parts_eight_choosable
#print axioms Se20Part.list_block_extension
#print axioms Se20Part.list_block_extension_of_iso
#print axioms Se20Part.threePart_five_degree
#print axioms Se20Part.threePart_five_block_extension
#print axioms Se20Part.petersenMinus_block_extension
#print axioms Se20Part.petersen_fifteen_edges
#print axioms Se20Part.petersen_cubic
#print axioms Se20Part.petersenEdge_injective
#print axioms Se20Part.petersenEdge_conflict
#print axioms Se20Part.petersenConflictIso
#print axioms Se20Part.petersen_eight_choosable
#print axioms Se20Part.induced_petersen_extension
#print axioms Se20Part.critical21_disjoint_of_extension
#print axioms Se20Part.critical21_disjoint_induced_petersen
#print axioms Se20Part.componentEdges_closed
#print axioms Se20Part.componentEdges_card_le_twice
#print axioms Se20Part.critical21_disjoint_small_closed
#print axioms Se20Part.critical21_disjoint_component_sixteen
#print axioms Se20Part.TwoRepresentativeSizeChecks.table
#print axioms Se20Part.TwoRepresentativeSizeChecks.checked_bounds
#print axioms Se20Part.TwoRepresentativeSizeChecks.size_bound

-- Fourth pass: explicit choices and ambient geometry for cut gluing.
#print axioms Se20Part.matching_cut_four_prescribed
#print axioms Se20Part.five_stars_single_hall
#print axioms Se20Part.five_stars_failure_counts
#print axioms Se20Part.five_stars_source_choices
#print axioms Se20Part.matching_cut_five_prescribed
#print axioms Se20Part.five_two_stars_robust
#print axioms Se20Part.robust_five_representatives
#print axioms Se20Part.single_allowed_candidates
#print axioms Se20Part.five_cut_forced_targets
#print axioms Se20Part.palette_complete_prescribed
#print axioms Se20Part.palette_complete_five
#print axioms Se20Part.matching_cut_five_palette
#print axioms Se20Part.matching_cut_small_palette
#print axioms Se20Part.cut_endpoint_budgets
#print axioms Se20Part.cut_cross_conflict_iff
#print axioms Se20Part.MatchingCut.cut_conflict_near
#print axioms Se20Part.matching_five_cut_gluing
#print axioms Se20Part.side_colourable_iff
#print axioms Se20Part.matching_cut_gluing
#print axioms Se20Part.matching_cut_strongColourable
#print axioms Se20Part.representatives_three_four
#print axioms Se20Part.repeated_cut_small_palette
#print axioms Se20Part.LabelledCut.endpoint_budgets
#print axioms Se20Part.LabelledCut.conflict_cover
#print axioms Se20Part.LabelledCut.boundary_colour_budget
#print axioms Se20Part.LabelledCut.sourceList_three
#print axioms Se20Part.LabelledCut.sourceList_large
#print axioms Se20Part.LabelledCut.targetList_five
#print axioms Se20Part.repeated_small_cut_gluing
#print axioms Se20Part.small_cut_strongColourable
#print axioms Se20Part.cutBoundary_degree_sum
#print axioms Se20Part.fourRegular_cut_even
#print axioms Se20Part.fourRegular_nontrivial_cut_six
#print axioms Se20Part.cutBoundary_erase_identity
#print axioms Se20Part.InducedMinimalCounterexample.cut_three
#print axioms Se20Part.InducedMinimalCounterexample.preconnected
#print axioms Se20Part.InducedMinimalCounterexample.nontrivial_cut_five
#print axioms Se20Part.InducedMinimalCounterexample.regular_nontrivial_cut_six
#print axioms Se20Part.InducedMinimalCounterexample.degree_three
#print axioms Se20Part.InducedMinimalCounterexample.no_matching_five_cut
#print axioms Se20Part.InducedMinimalCounterexample.regular_cut_four
#print axioms Se20Part.InducedMinimalCounterexample.no_small_separator
#print axioms Se20Part.InducedMinimalCounterexample.delete_two_connected
#print axioms Se20Part.adjacent_colouredStars_inter_le_one
#print axioms Se20Part.equal_colouredStars_nonadjacent
#print axioms Se20Part.k33_palette_failure
#print axioms Se20Part.selected_conflicts_le_fifteen
#print axioms Se20Part.petersen_selected_degree_one
#print axioms Se20Part.critical21_no_supported_induced_petersen
#print axioms Se20Part.petersenMinusEdge_conflict
#print axioms Se20Part.petersenMinus_short_paths
#print axioms Se20Part.petersenMinus_only_missing_chord
#print axioms Se20Part.induced_petersenMinus_extension
#print axioms Se20Part.critical21_disjoint_induced_petersenMinus
#print axioms Se20Part.minimal_low_bad_lists
#print axioms Se20Part.minimal_low_block_classification
#print axioms Se20Part.selected_conflicts_le_eighteen
#print axioms Se20Part.petersenMinus_selected_degree_two
#print axioms Se20Part.critical21_no_supported_induced_petersenMinus
#print axioms Se20Part.critical21_no_supported_petersenMinus_subgraph
#print axioms Se20Part.petersen_common_neighbour
#print axioms Se20Part.inducedPetersenOfGirth
#print axioms Se20Part.greedy_partial_extension
#print axioms Se20Part.petersen_spokes_matching
#print axioms Se20Part.petersen_spoke_outside_conflicts
#print axioms Se20Part.petersen_incident_extension
#print axioms Se20Part.critical21_no_supported_petersen_subgraph
#print axioms Se20Part.colourable_of_clique_separator
#print axioms Se20Part.minimal_noncolourable_no_clique_separator

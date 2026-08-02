import Exercises.FieldTheory.«02FiniteFields»
import Solutions.FieldTheory.«02FiniteFields»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.FieldTheory.FiniteFields.q1_card_of_basis [FiniteField.card]
assert_not_uses Exercises.FieldTheory.FiniteFields.q2_card_prime_power [FiniteField.card]
assert_not_uses Exercises.FieldTheory.FiniteFields.q3_galois_field_card [GaloisField.card]
assert_not_uses Exercises.FieldTheory.FiniteFields.q5_fermat_f7 [ZMod.pow_card]

assert_not_uses Solutions.FieldTheory.FiniteFields.q1_card_of_basis [FiniteField.card]
assert_not_uses Solutions.FieldTheory.FiniteFields.q2_card_prime_power [FiniteField.card]
assert_not_uses Solutions.FieldTheory.FiniteFields.q3_galois_field_card [GaloisField.card]
assert_not_uses Solutions.FieldTheory.FiniteFields.q5_fermat_f7 [ZMod.pow_card]

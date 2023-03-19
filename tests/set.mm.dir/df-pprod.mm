
axiom df-pprod
  let cA: class A
  let cB: class B
  assert |- pprod ( A , B ) = ( ( A o. ( 1st |` ( _V X. _V ) ) ) (x) ( B o. ( 2nd |` ( _V X. _V ) ) ) )
end


axiom ax-oadist
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wve: term e
  param wvf: term f
  param wvh: term h
  param wvj: term j
  param wvk: term k
  assume oad.1: |- e = ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) )
  assume oad.2: |- f = ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v e )
  assume oad.3: |- h =< ( a ->1 d )
  assume oad.4: |- j =< f
  assume oad.5: |- k =< f
  assume oad.6: |- ( h ^ ( b ->1 d ) ) =< k
  assert |- ( h ^ ( j v k ) ) = ( ( h ^ j ) v ( h ^ k ) )
end

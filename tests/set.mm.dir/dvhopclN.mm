include "opelxpi.mm"

theorem dvhopclN
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F


  assert |- ( ( F e. T /\ U e. E ) -> <. F , U >. e. ( T X. E ) )

  proof
    cF
    cU
    cT
    cE
    opelxpi
end

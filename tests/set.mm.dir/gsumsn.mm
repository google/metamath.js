include "nfcv.mm"
include "gsumsnf.mm"

theorem gsumsn
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cV: class V
  assume gsumsn.b: |- B = ( Base ` G )
  assume gsumsn.s: |- ( k = M -> A = C )

  disjoint B k
  disjoint C k
  disjoint G k
  disjoint M k
  disjoint V k
  assert |- ( ( G e. Mnd /\ M e. V /\ C e. B ) -> ( G gsum ( k e. { M } |-> A ) ) = C )

  proof
    cA
    cB
    cC
    vk
    cG
    cM
    cV
    vk
    cC
    nfcv
    gsumsn.b
    gsumsn.s
    gsumsnf
end

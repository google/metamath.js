include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cfn.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "crab.mm"
include "wss.mm"
include "fzfi.mm"
include "prmnn.mm"
include "ssriv.mm"
include "rabss2.mm"
include "ax-mp.mm"
include "dvdsssfz1.mm"
include "syl5ss.mm"
include "ssfi.mm"
include "sylancr.mm"

theorem prmdvdsfi
  let cA: class A
  let vp: setvar p
  let vk: setvar k
  let vn: setvar n
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P

  disjoint A p
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q s
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint K p
  disjoint M p
  disjoint M x
  disjoint N p
  disjoint S s
  disjoint S x
  disjoint B k
  disjoint B n
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P p
  assert |- ( A e. NN -> { p e. Prime | p || A } e. Fin )

  proof
    cA
    cn
    wcel
    #
    c1
    cA
    cfz
    co
    #
    cfn
    wcel
    vp
    cv
    #
    cA
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    @1
    wss
    @4
    cfn
    wcel
    c1
    cA
    fzfi
    @0
    @4
    @3
    vp
    cn
    crab
    #
    @1
    cprime
    cn
    wss
    @4
    @5
    wss
    vp
    cprime
    cn
    @2
    prmnn
    ssriv
    @3
    vp
    cprime
    cn
    rabss2
    ax-mp
    cA
    vp
    dvdsssfz1
    syl5ss
    @1
    @4
    ssfi
    sylancr
end

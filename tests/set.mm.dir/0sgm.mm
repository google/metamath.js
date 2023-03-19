include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "csgm.mm"
include "co.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cexp.mm"
include "csu.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmul.mm"
include "cz.mm"
include "wceq.mm"
include "0z.mm"
include "sgmval2.mm"
include "mpan.mm"
include "elrabi.mm"
include "nncnd.mm"
include "exp0d.mm"
include "sumeq2i.mm"
include "cfn.mm"
include "cc.mm"
include "cfz.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "ax-1cn.mm"
include "fsumconst.mm"
include "sylancl.mm"
include "syl5eq.mm"
include "cn0.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "3eqtrd.mm"

theorem 0sgm
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
  assert |- ( A e. NN -> ( 0 sigma A ) = ( # ` { p e. NN | p || A } ) )

  proof
    cA
    cn
    wcel
    #
    cc0
    cA
    csgm
    co
    #
    vp
    cv
    cA
    cdvds
    wbr
    #
    vp
    cn
    crab
    #
    vk
    cv
    #
    cc0
    cexp
    co
    #
    vk
    csu
    #
    @3
    chash
    cfv
    #
    c1
    cmul
    co
    #
    @7
    cc0
    cz
    wcel
    @0
    @1
    @6
    wceq
    0z
    cc0
    cA
    vk
    vp
    sgmval2
    mpan
    @0
    @6
    @3
    c1
    vk
    csu
    #
    @8
    @3
    @5
    c1
    vk
    @4
    @3
    wcel
    #
    @4
    @10
    @4
    @2
    vp
    @4
    cn
    elrabi
    nncnd
    exp0d
    sumeq2i
    @0
    @3
    cfn
    wcel
    #
    c1
    cc
    wcel
    @9
    @8
    wceq
    @0
    c1
    cA
    cfz
    co
    #
    cfn
    wcel
    @3
    @12
    wss
    @11
    @0
    c1
    cA
    fzfid
    cA
    vp
    dvdsssfz1
    @12
    @3
    ssfi
    syl2anc
    #
    ax-1cn
    @3
    c1
    vk
    fsumconst
    sylancl
    syl5eq
    @0
    @7
    @0
    @7
    @0
    @11
    @7
    cn0
    wcel
    @13
    @3
    hashcl
    syl
    nn0cnd
    mulid1d
    3eqtrd
end

include "cn.mm"
include "wcel.mm"
include "cmu.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "wn.mm"
include "c1.mm"
include "cneg.mm"
include "crab.mm"
include "chash.mm"
include "cif.mm"
include "wne.mm"
include "cz.mm"
include "cfn.mm"
include "cn0.mm"
include "prmdvdsfi.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0zd.mm"
include "cc.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "expne0i.mm"
include "mp3an12.mm"
include "iffalse.mm"
include "neeq1d.mm"
include "syl5ibrcom.mm"
include "muval.mm"
include "sylibrd.mm"
include "necon4bd.mm"
include "iftrue.mm"
include "eqeq1d.mm"
include "syl5ibr.mm"
include "impbid.mm"

theorem isnsqf
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
  assert |- ( A e. NN -> ( ( mmu ` A ) = 0 <-> E. p e. Prime ( p ^ 2 ) || A ) )

  proof
    cA
    cn
    wcel
    #
    cA
    cmu
    cfv
    #
    cc0
    wceq
    #
    vp
    cv
    #
    c2
    cexp
    co
    cA
    cdvds
    wbr
    vp
    cprime
    wrex
    #
    @0
    @4
    @1
    cc0
    @0
    @4
    wn
    #
    @4
    cc0
    c1
    cneg
    #
    @3
    cA
    cdvds
    wbr
    vp
    cprime
    crab
    #
    chash
    cfv
    #
    cexp
    co
    #
    cif
    #
    cc0
    wne
    #
    @1
    cc0
    wne
    @0
    @11
    @5
    @9
    cc0
    wne
    #
    @0
    @8
    cz
    wcel
    #
    @12
    @0
    @8
    @0
    @7
    cfn
    wcel
    @8
    cn0
    wcel
    cA
    vp
    prmdvdsfi
    @7
    hashcl
    syl
    nn0zd
    @6
    cc
    wcel
    @6
    cc0
    wne
    @13
    @12
    neg1cn
    neg1ne0
    @6
    @8
    expne0i
    mp3an12
    syl
    @5
    @10
    @9
    cc0
    @4
    cc0
    @9
    iffalse
    neeq1d
    syl5ibrcom
    @0
    @1
    @10
    cc0
    cA
    vp
    muval
    #
    neeq1d
    sylibrd
    necon4bd
    @4
    @2
    @0
    @10
    cc0
    wceq
    @4
    cc0
    @9
    iftrue
    @0
    @1
    @10
    cc0
    @14
    eqeq1d
    syl5ibr
    impbid
end

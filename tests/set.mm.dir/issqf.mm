include "cn.mm"
include "wcel.mm"
include "cmu.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "wn.mm"
include "cpc.mm"
include "c1.mm"
include "cle.mm"
include "wral.mm"
include "isnsqf.mm"
include "necon3abid.mm"
include "ralnex.mm"
include "wa.mm"
include "clt.mm"
include "caddc.mm"
include "cn0.mm"
include "wb.mm"
include "1nn0.mm"
include "pccl.mm"
include "ancoms.mm"
include "nn0ltp1le.mm"
include "sylancr.mm"
include "cr.mm"
include "1re.mm"
include "nn0red.mm"
include "ltnle.mm"
include "df-2.mm"
include "breq1i.mm"
include "cz.mm"
include "id.mm"
include "nnz.mm"
include "2nn0.mm"
include "pcdvdsb.mm"
include "mp3an3.mm"
include "syl2anr.mm"
include "syl5bbr.mm"
include "3bitr3d.mm"
include "con1bid.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem issqf
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
  assert |- ( A e. NN -> ( ( mmu ` A ) =/= 0 <-> A. p e. Prime ( p pCnt A ) <_ 1 ) )

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
    wne
    vp
    cv
    #
    c2
    cexp
    co
    cA
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    wn
    #
    @2
    cA
    cpc
    co
    #
    c1
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @0
    @4
    @1
    cc0
    cA
    vp
    isnsqf
    necon3abid
    @5
    @3
    wn
    #
    vp
    cprime
    wral
    @0
    @8
    @3
    vp
    cprime
    ralnex
    @0
    @9
    @7
    vp
    cprime
    @0
    @2
    cprime
    wcel
    #
    wa
    #
    @7
    @3
    @11
    c1
    @6
    clt
    wbr
    #
    c1
    c1
    caddc
    co
    #
    @6
    cle
    wbr
    #
    @7
    wn
    #
    @3
    @11
    c1
    cn0
    wcel
    @6
    cn0
    wcel
    #
    @12
    @14
    wb
    1nn0
    @10
    @0
    @16
    @2
    cA
    pccl
    ancoms
    #
    c1
    @6
    nn0ltp1le
    sylancr
    @11
    c1
    cr
    wcel
    @6
    cr
    wcel
    @12
    @15
    wb
    1re
    @11
    @6
    @17
    nn0red
    c1
    @6
    ltnle
    sylancr
    @14
    c2
    @6
    cle
    wbr
    #
    @11
    @3
    c2
    @13
    @6
    cle
    df-2
    breq1i
    @10
    @10
    cA
    cz
    wcel
    #
    @18
    @3
    wb
    #
    @0
    @10
    id
    cA
    nnz
    @10
    @19
    c2
    cn0
    wcel
    @20
    2nn0
    c2
    @2
    cA
    pcdvdsb
    mp3an3
    syl2anr
    syl5bbr
    3bitr3d
    con1bid
    ralbidva
    syl5bbr
    bitrd
end

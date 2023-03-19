include "cn.mm"
include "wcel.mm"
include "cvma.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "crab.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "cuni.mm"
include "clog.mm"
include "cif.mm"
include "wreu.mm"
include "eqid.mm"
include "vmaval.mm"
include "neeq1d.mm"
include "c1o.mm"
include "cen.mm"
include "reuen1.mm"
include "wa.mm"
include "hash1.mm"
include "eqeq2i.mm"
include "cfn.mm"
include "wb.mm"
include "prmdvdsfi.mm"
include "com.mm"
include "1onn.mm"
include "nnfi.mm"
include "ax-mp.mm"
include "hashen.mm"
include "sylancl.mm"
include "syl5bbr.mm"
include "biimpar.mm"
include "iftrued.mm"
include "c2.mm"
include "cuz.mm"
include "cr.mm"
include "csn.mm"
include "wss.mm"
include "simpr.mm"
include "en1b.mm"
include "sylib.mm"
include "ssrab2.mm"
include "syl6eqssr.mm"
include "cvv.mm"
include "uniexg.mm"
include "syl.mm"
include "adantr.mm"
include "snssg.mm"
include "mpbird.mm"
include "prmuz2.mm"
include "eluzelre.mm"
include "clt.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "rplogcld.mm"
include "rpne0d.mm"
include "eqnetrd.mm"
include "ex.mm"
include "iffalse.mm"
include "necon1ai.mm"
include "syl5ib.mm"
include "impbid.mm"
include "syl5bb.mm"
include "bitr4d.mm"

theorem isppw
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
  assert |- ( A e. NN -> ( ( Lam ` A ) =/= 0 <-> E! p e. Prime p || A ) )

  proof
    cA
    cn
    wcel
    #
    cA
    cvma
    cfv
    #
    cc0
    wne
    vp
    cv
    cA
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    chash
    cfv
    #
    c1
    wceq
    #
    @3
    cuni
    #
    clog
    cfv
    #
    cc0
    cif
    #
    cc0
    wne
    #
    @2
    vp
    cprime
    wreu
    #
    @0
    @1
    @8
    cc0
    cA
    @3
    vp
    @3
    eqid
    vmaval
    neeq1d
    @10
    @3
    c1o
    cen
    wbr
    #
    @0
    @9
    @2
    vp
    cprime
    reuen1
    @0
    @11
    @9
    @0
    @11
    @9
    @0
    @11
    wa
    #
    @8
    @7
    cc0
    @12
    @5
    @7
    cc0
    @0
    @5
    @11
    @5
    @4
    c1o
    chash
    cfv
    #
    wceq
    #
    @0
    @11
    @13
    c1
    @4
    hash1
    eqeq2i
    @0
    @3
    cfn
    wcel
    #
    c1o
    cfn
    wcel
    #
    @14
    @11
    wb
    cA
    vp
    prmdvdsfi
    #
    c1o
    com
    wcel
    @16
    1onn
    c1o
    nnfi
    ax-mp
    @3
    c1o
    hashen
    sylancl
    syl5bbr
    #
    biimpar
    iftrued
    @12
    @7
    @12
    @6
    @12
    @6
    c2
    cuz
    cfv
    wcel
    #
    @6
    cr
    wcel
    @12
    @6
    cprime
    wcel
    #
    @19
    @12
    @20
    @6
    csn
    #
    cprime
    wss
    #
    @12
    @21
    @3
    cprime
    @12
    @11
    @3
    @21
    wceq
    @0
    @11
    simpr
    @3
    en1b
    sylib
    @2
    vp
    cprime
    ssrab2
    syl6eqssr
    @12
    @6
    cvv
    wcel
    #
    @20
    @22
    wb
    @0
    @23
    @11
    @0
    @15
    @23
    @17
    @3
    cfn
    uniexg
    syl
    adantr
    @6
    cprime
    cvv
    snssg
    syl
    mpbird
    @6
    prmuz2
    syl
    #
    c2
    @6
    eluzelre
    syl
    @12
    @19
    c1
    @6
    clt
    wbr
    #
    @24
    @19
    @6
    cn
    wcel
    @25
    @6
    eluz2b2
    simprbi
    syl
    rplogcld
    rpne0d
    eqnetrd
    ex
    @9
    @5
    @0
    @11
    @5
    @8
    cc0
    @5
    @7
    cc0
    iffalse
    necon1ai
    @18
    syl5ib
    impbid
    syl5bb
    bitr4d
end

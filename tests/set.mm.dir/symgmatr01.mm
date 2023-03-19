include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "cdif.mm"
include "cif.mm"
include "co.mm"
include "cmpt2.mm"
include "wrex.mm"
include "symgmatr01lem.mm"
include "imp.mm"
include "cvv.mm"
include "eqidd.mm"
include "weq.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantr.mm"
include "adantl.mm"
include "ifbid.mm"
include "oveq12.mm"
include "ifbieq12d.mm"
include "simpr.mm"
include "wi.mm"
include "eldifi.mm"
include "csymg.mm"
include "eqid.mm"
include "symgfv.mm"
include "ex.mm"
include "syl.mm"
include "cur.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c0g.mm"
include "ifex.mm"
include "ovex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "eqeq1d.mm"
include "rexbidva.mm"
include "mpbird.mm"

theorem symgmatr01
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vq: setvar q
  let cA: class A
  let cB: class B
  assume symgmatr01.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume symgmatr01.0: |- .0. = ( 0g ` R )
  assume symgmatr01.1: |- .1. = ( 1r ` R )

  disjoint k q
  disjoint L k
  disjoint L q
  disjoint K k
  disjoint K q
  disjoint M k
  disjoint N k
  disjoint P k
  disjoint P q
  disjoint Q k
  disjoint Q q
  disjoint i j
  disjoint i k
  disjoint i q
  disjoint L i
  disjoint j k
  disjoint j q
  disjoint L j
  disjoint K i
  disjoint K j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint Q i
  disjoint Q j
  disjoint .1. i
  disjoint .1. j
  disjoint .1. k
  disjoint .0. i
  disjoint .0. j
  disjoint .0. k
  disjoint A k
  disjoint B k
  assert |- ( ( K e. N /\ L e. N ) -> ( Q e. ( P \ { q e. P | ( q ` K ) = L } ) -> E. k e. N ( k ( i e. N , j e. N |-> if ( i = K , if ( j = L , .1. , .0. ) , ( i M j ) ) ) ( Q ` k ) ) = .0. ) )

  proof
    cK
    cN
    wcel
    cL
    cN
    wcel
    wa
    #
    cQ
    cP
    cK
    vq
    cv
    cfv
    cL
    wceq
    vq
    cP
    crab
    #
    cdif
    wcel
    #
    vk
    cv
    #
    @3
    cQ
    cfv
    #
    vi
    vj
    cN
    cN
    vi
    cv
    #
    cK
    wceq
    #
    vj
    cv
    #
    cL
    wceq
    #
    c.1
    c.0
    cif
    #
    @5
    @7
    cM
    co
    #
    cif
    #
    cmpt2
    #
    co
    #
    c.0
    wceq
    #
    vk
    cN
    wrex
    #
    @0
    @2
    wa
    #
    @15
    @3
    cK
    wceq
    #
    @4
    cL
    wceq
    #
    c.1
    c.0
    cif
    #
    @3
    @4
    cM
    co
    #
    cif
    #
    c.0
    wceq
    #
    vk
    cN
    wrex
    #
    @0
    @2
    @23
    c.1
    c.0
    cP
    cQ
    vk
    cK
    cL
    cM
    cN
    vq
    symgmatr01.p
    symgmatr01lem
    imp
    @16
    @14
    @22
    vk
    cN
    @16
    @3
    cN
    wcel
    #
    wa
    #
    @13
    @21
    c.0
    @25
    vi
    vj
    @3
    @4
    cN
    cN
    @11
    @21
    @12
    cvv
    @25
    @12
    eqidd
    vi
    vk
    weq
    #
    @7
    @4
    wceq
    #
    wa
    #
    @11
    @21
    wceq
    @25
    @28
    @6
    @17
    @9
    @10
    @19
    @20
    @26
    @6
    @17
    wb
    @27
    @5
    @3
    cK
    eqeq1
    adantr
    @28
    @8
    @18
    c.1
    c.0
    @27
    @8
    @18
    wb
    @26
    @7
    @4
    cL
    eqeq1
    adantl
    ifbid
    @5
    @3
    @7
    @4
    cM
    oveq12
    ifbieq12d
    adantl
    @16
    @24
    simpr
    @16
    @24
    @4
    cN
    wcel
    #
    @2
    @24
    @29
    wi
    #
    @0
    @2
    cQ
    cP
    wcel
    #
    @30
    cQ
    cP
    @1
    eldifi
    @31
    @24
    @29
    cN
    cP
    cQ
    cN
    csymg
    cfv
    #
    @3
    @32
    eqid
    symgmatr01.p
    symgfv
    ex
    syl
    adantl
    imp
    @21
    cvv
    wcel
    @25
    @17
    @19
    @20
    @18
    c.1
    c.0
    c.1
    cR
    cur
    cfv
    cvv
    symgmatr01.1
    cR
    cur
    fvex
    eqeltri
    c.0
    cR
    c0g
    cfv
    cvv
    symgmatr01.0
    cR
    c0g
    fvex
    eqeltri
    ifex
    @3
    @4
    cM
    ovex
    ifex
    a1i
    ovmpt2d
    eqeq1d
    rexbidva
    mpbird
    ex
end

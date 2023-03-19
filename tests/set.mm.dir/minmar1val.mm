include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "weq.mm"
include "cif.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "wceq.mm"
include "minmar1val0.mm"
include "3ad2ant1.mm"
include "cvv.mm"
include "simp2.mm"
include "simpl3.mm"
include "wa.mm"
include "cfn.mm"
include "matrcl.mm"
include "simpld.mm"
include "jca.mm"
include "adantr.mm"
include "mpt2exga.mm"
include "syl.mm"
include "wb.mm"
include "eqeq2.mm"
include "ifbid.mm"
include "adantl.mm"
include "ifbieq1d.mm"
include "mpt2eq3dv.mm"
include "ovmpt2dv2.mm"
include "mpd.mm"

theorem minmar1val
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vk: setvar k
  let vl: setvar l
  assume minmar1fval.a: |- A = ( N Mat R )
  assume minmar1fval.b: |- B = ( Base ` A )
  assume minmar1fval.q: |- Q = ( N minMatR1 R )
  assume minmar1fval.o: |- .1. = ( 1r ` R )
  assume minmar1fval.z: |- .0. = ( 0g ` R )

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint M i
  disjoint M j
  disjoint K i
  disjoint K j
  disjoint L i
  disjoint L j
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint N k
  disjoint N l
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint k l
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint l m
  disjoint l n
  disjoint l r
  disjoint R k
  disjoint R l
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint .1. n
  disjoint .1. r
  disjoint .0. n
  disjoint .0. r
  disjoint M k
  disjoint M l
  disjoint M m
  disjoint .1. m
  disjoint .0. m
  disjoint B k
  disjoint B l
  disjoint K k
  disjoint K l
  disjoint L k
  disjoint L l
  disjoint .1. k
  disjoint .1. l
  disjoint .0. k
  disjoint .0. l
  assert |- ( ( M e. B /\ K e. N /\ L e. N ) -> ( K ( Q ` M ) L ) = ( i e. N , j e. N |-> if ( i = K , if ( j = L , .1. , .0. ) , ( i M j ) ) ) )

  proof
    cM
    cB
    wcel
    #
    cK
    cN
    wcel
    #
    cL
    cN
    wcel
    #
    w3a
    #
    cM
    cQ
    cfv
    #
    vk
    vl
    cN
    cN
    vi
    vj
    cN
    cN
    vi
    vk
    weq
    #
    vj
    vl
    weq
    #
    c.1
    c.0
    cif
    #
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cif
    #
    cmpt2
    #
    cmpt2
    wceq
    #
    cK
    cL
    @4
    co
    vi
    vj
    cN
    cN
    @8
    cK
    wceq
    #
    @9
    cL
    wceq
    #
    c.1
    c.0
    cif
    #
    @10
    cif
    #
    cmpt2
    #
    wceq
    @0
    @1
    @13
    @2
    cA
    cB
    cQ
    cR
    c.1
    vi
    vj
    vk
    cM
    cN
    c.0
    vl
    minmar1fval.a
    minmar1fval.b
    minmar1fval.q
    minmar1fval.o
    minmar1fval.z
    minmar1val0
    3ad2ant1
    @3
    vk
    vl
    cK
    cL
    cN
    cN
    @12
    @18
    @4
    cvv
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    vk
    cv
    #
    cK
    wceq
    #
    simpl3
    @3
    @20
    vl
    cv
    #
    cL
    wceq
    #
    wa
    #
    wa
    cN
    cfn
    wcel
    #
    @24
    wa
    #
    @12
    cvv
    wcel
    @3
    @25
    @23
    @0
    @1
    @25
    @2
    @0
    @24
    @24
    @0
    @24
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    minmar1fval.a
    minmar1fval.b
    matrcl
    simpld
    #
    @26
    jca
    3ad2ant1
    adantr
    vi
    vj
    cN
    cN
    @11
    cfn
    cfn
    mpt2exga
    syl
    @23
    @12
    @18
    wceq
    @3
    @23
    vi
    vj
    cN
    cN
    @11
    @17
    @23
    @5
    @14
    @7
    @16
    @10
    @20
    @5
    @14
    wb
    @22
    @19
    cK
    @8
    eqeq2
    adantr
    @22
    @7
    @16
    wceq
    @20
    @22
    @6
    @15
    c.1
    c.0
    @21
    cL
    @9
    eqeq2
    ifbid
    adantl
    ifbieq1d
    mpt2eq3dv
    adantl
    ovmpt2dv2
    mpd
end

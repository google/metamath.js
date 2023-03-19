include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "co.mm"
include "cmpt2.mm"
include "wceq.mm"
include "submaval0.mm"
include "3ad2ant1.mm"
include "cvv.mm"
include "simp2.mm"
include "simpl3.mm"
include "wa.mm"
include "cfn.mm"
include "matrcl.mm"
include "simpld.mm"
include "diffi.mm"
include "syl.mm"
include "jca.mm"
include "adantr.mm"
include "mpt2exga.mm"
include "sneq.mm"
include "difeq2d.mm"
include "adantl.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "ovmpt2dv2.mm"
include "mpd.mm"

theorem submaval
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vk: setvar k
  let vl: setvar l
  assume submafval.a: |- A = ( N Mat R )
  assume submafval.q: |- Q = ( N subMat R )
  assume submafval.b: |- B = ( Base ` A )

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
  disjoint M k
  disjoint M l
  disjoint M m
  disjoint B k
  disjoint B l
  disjoint K k
  disjoint K l
  disjoint L k
  disjoint L l
  assert |- ( ( M e. B /\ K e. N /\ L e. N ) -> ( K ( Q ` M ) L ) = ( i e. ( N \ { K } ) , j e. ( N \ { L } ) |-> ( i M j ) ) )

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
    vk
    cv
    #
    csn
    #
    cdif
    #
    cN
    vl
    cv
    #
    csn
    #
    cdif
    #
    vi
    cv
    vj
    cv
    cM
    co
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
    cK
    csn
    #
    cdif
    #
    cN
    cL
    csn
    #
    cdif
    #
    @11
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
    vi
    vj
    vk
    cM
    cN
    vl
    submafval.a
    submafval.q
    submafval.b
    submaval0
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
    @5
    cK
    wceq
    #
    simpl3
    @3
    @19
    @8
    cL
    wceq
    #
    wa
    #
    wa
    @7
    cfn
    wcel
    #
    @10
    cfn
    wcel
    #
    wa
    #
    @12
    cvv
    wcel
    @3
    @24
    @21
    @0
    @1
    @24
    @2
    @0
    @22
    @23
    @0
    cN
    cfn
    wcel
    #
    @22
    @0
    @25
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    submafval.a
    submafval.b
    matrcl
    simpld
    #
    cN
    @6
    diffi
    syl
    @0
    @25
    @23
    @26
    cN
    @9
    diffi
    syl
    jca
    3ad2ant1
    adantr
    vi
    vj
    @7
    @10
    @11
    cfn
    cfn
    mpt2exga
    syl
    @21
    @12
    @18
    wceq
    @3
    @21
    vi
    vj
    @7
    @10
    @11
    @15
    @17
    @11
    @19
    @7
    @15
    wceq
    @20
    @19
    @6
    @14
    cN
    @5
    cK
    sneq
    difeq2d
    adantr
    @20
    @10
    @17
    wceq
    @19
    @20
    @9
    @16
    cN
    @8
    cL
    sneq
    difeq2d
    adantl
    @21
    @11
    eqidd
    mpt2eq123dv
    adantl
    ovmpt2dv2
    mpd
end

include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "co.mm"
include "weq.mm"
include "cif.mm"
include "cv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "marrepval0.mm"
include "adantr.mm"
include "cvv.mm"
include "simprl.mm"
include "simplrr.mm"
include "cfn.mm"
include "matrcl.mm"
include "simpld.mm"
include "jca.mm"
include "ad3antrrr.mm"
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

theorem marrepval
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
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
  let vs: setvar s
  let vk: setvar k
  let vl: setvar l
  assume marrepfval.a: |- A = ( N Mat R )
  assume marrepfval.b: |- B = ( Base ` A )
  assume marrepfval.q: |- Q = ( N matRRep R )
  assume marrepfval.z: |- .0. = ( 0g ` R )

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint M i
  disjoint M j
  disjoint S i
  disjoint S j
  disjoint K i
  disjoint K j
  disjoint L i
  disjoint L j
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint B s
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint n r
  disjoint n s
  disjoint r s
  disjoint N k
  disjoint N l
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint N s
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i s
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint j s
  disjoint k l
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint l m
  disjoint l n
  disjoint l r
  disjoint l s
  disjoint R k
  disjoint R l
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint R s
  disjoint .0. n
  disjoint .0. r
  disjoint M k
  disjoint M l
  disjoint M m
  disjoint M s
  disjoint S k
  disjoint S l
  disjoint S m
  disjoint S s
  disjoint .0. m
  disjoint .0. s
  disjoint B k
  disjoint B l
  disjoint K k
  disjoint K l
  disjoint L k
  disjoint L l
  disjoint .0. k
  disjoint .0. l
  assert |- ( ( ( M e. B /\ S e. ( Base ` R ) ) /\ ( K e. N /\ L e. N ) ) -> ( K ( M Q S ) L ) = ( i e. N , j e. N |-> if ( i = K , if ( j = L , S , .0. ) , ( i M j ) ) ) )

  proof
    cM
    cB
    wcel
    #
    cS
    cR
    cbs
    cfv
    wcel
    #
    wa
    #
    cK
    cN
    wcel
    #
    cL
    cN
    wcel
    #
    wa
    #
    wa
    #
    cM
    cS
    cQ
    co
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
    cS
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
    @7
    co
    vi
    vj
    cN
    cN
    @11
    cK
    wceq
    #
    @12
    cL
    wceq
    #
    cS
    c.0
    cif
    #
    @13
    cif
    #
    cmpt2
    #
    wceq
    @2
    @16
    @5
    cA
    cB
    cQ
    cR
    cS
    vi
    vj
    vk
    cM
    cN
    c.0
    vl
    marrepfval.a
    marrepfval.b
    marrepfval.q
    marrepfval.z
    marrepval0
    adantr
    @6
    vk
    vl
    cK
    cL
    cN
    cN
    @15
    @21
    @7
    cvv
    @2
    @3
    @4
    simprl
    @2
    @3
    @4
    vk
    cv
    #
    cK
    wceq
    #
    simplrr
    @6
    @23
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
    @27
    wa
    #
    @15
    cvv
    wcel
    @0
    @28
    @1
    @5
    @26
    @0
    @27
    @27
    @0
    @27
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    marrepfval.a
    marrepfval.b
    matrcl
    simpld
    #
    @29
    jca
    ad3antrrr
    vi
    vj
    cN
    cN
    @14
    cfn
    cfn
    mpt2exga
    syl
    @26
    @15
    @21
    wceq
    @6
    @26
    vi
    vj
    cN
    cN
    @14
    @20
    @26
    @8
    @17
    @10
    @19
    @13
    @23
    @8
    @17
    wb
    @25
    @22
    cK
    @11
    eqeq2
    adantr
    @25
    @10
    @19
    wceq
    @23
    @25
    @9
    @18
    cS
    c.0
    @24
    cL
    @12
    eqeq2
    ifbid
    adantl
    ifbieq1d
    mpt2eq3dv
    adantl
    ovmpt2dv2
    mpd
end

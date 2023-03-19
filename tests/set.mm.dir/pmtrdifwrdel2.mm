include "wcel.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cword.mm"
include "wrex.mm"
include "cid.mm"
include "cdm.mm"
include "cpmtr.mm"
include "cmpt.mm"
include "weq.mm"
include "fveq2.mm"
include "difeq1d.mm"
include "dmeqd.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "pmtrdifwrdellem1.mm"
include "adantl.mm"
include "pmtrdifwrdellem2.mm"
include "pmtrdifwrdel2lem1.mm"
include "ancoms.mm"
include "pmtrdifwrdellem3.mm"
include "r19.26.mm"
include "sylanbrc.mm"
include "eqeq2d.mm"
include "fveq1.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ralrimiva.mm"

theorem pmtrdifwrdel2
  let vx: setvar x
  let vw: setvar w
  let vu: setvar u
  let cR: class R
  let cT: class T
  let vi: setvar i
  let cK: class K
  let cN: class N
  let vr: setvar r
  let vt: setvar t
  let vj: setvar j
  let vn: setvar n
  assume pmtrdifel.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume pmtrdifel.r: |- R = ran ( pmTrsp ` N )

  disjoint N x
  disjoint T x
  disjoint K u
  disjoint N i
  disjoint N u
  disjoint i u
  disjoint T i
  disjoint R i
  disjoint R u
  disjoint i w
  disjoint i x
  disjoint u w
  disjoint u x
  disjoint w x
  disjoint K i
  disjoint K w
  disjoint N w
  disjoint r t
  disjoint r x
  disjoint t x
  disjoint K r
  disjoint N r
  disjoint R r
  disjoint N j
  disjoint N n
  disjoint i j
  disjoint i n
  disjoint j n
  disjoint j u
  disjoint n u
  disjoint T n
  disjoint R n
  disjoint j w
  disjoint j x
  disjoint n w
  disjoint n x
  assert |- ( K e. N -> A. w e. Word T E. u e. Word R ( ( # ` w ) = ( # ` u ) /\ A. i e. ( 0 ..^ ( # ` w ) ) ( ( ( u ` i ) ` K ) = K /\ A. x e. ( N \ { K } ) ( ( w ` i ) ` x ) = ( ( u ` i ) ` x ) ) ) )

  proof
    cK
    cN
    wcel
    #
    vw
    cv
    #
    chash
    cfv
    #
    vu
    cv
    #
    chash
    cfv
    #
    wceq
    #
    cK
    vi
    cv
    #
    @3
    cfv
    #
    cfv
    #
    cK
    wceq
    #
    vx
    cv
    #
    @6
    @1
    cfv
    cfv
    #
    @10
    @7
    cfv
    #
    wceq
    #
    vx
    cN
    cK
    csn
    cdif
    #
    wral
    #
    wa
    #
    vi
    cc0
    @2
    cfzo
    co
    #
    wral
    #
    wa
    #
    vu
    cR
    cword
    #
    wrex
    #
    vw
    cT
    cword
    #
    @0
    @1
    @22
    wcel
    #
    wa
    #
    vj
    @17
    vj
    cv
    #
    @1
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    cN
    cpmtr
    cfv
    #
    cfv
    #
    cmpt
    #
    @20
    wcel
    #
    @2
    @31
    chash
    cfv
    #
    wceq
    #
    cK
    @6
    @31
    cfv
    #
    cfv
    #
    cK
    wceq
    #
    @11
    @10
    @35
    cfv
    #
    wceq
    #
    vx
    @14
    wral
    #
    wa
    #
    vi
    @17
    wral
    #
    @21
    @23
    @32
    @0
    vn
    cR
    cT
    @31
    cK
    cN
    @1
    pmtrdifel.t
    pmtrdifel.r
    vj
    vn
    @17
    @30
    vn
    cv
    #
    @1
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    @29
    cfv
    vj
    vn
    weq
    #
    @28
    @46
    @29
    @47
    @27
    @45
    @47
    @26
    @44
    cid
    @25
    @43
    @1
    fveq2
    difeq1d
    dmeqd
    fveq2d
    cbvmptv
    #
    pmtrdifwrdellem1
    adantl
    @23
    @34
    @0
    vn
    cR
    cT
    @31
    cK
    cN
    @1
    pmtrdifel.t
    pmtrdifel.r
    @48
    pmtrdifwrdellem2
    adantl
    @24
    @37
    vi
    @17
    wral
    #
    @40
    vi
    @17
    wral
    #
    @42
    @23
    @0
    @49
    vn
    cR
    cT
    @31
    vi
    cK
    cN
    @1
    pmtrdifel.t
    pmtrdifel.r
    @48
    pmtrdifwrdel2lem1
    ancoms
    @23
    @50
    @0
    vn
    cR
    cT
    @31
    vi
    vx
    cK
    cN
    @1
    pmtrdifel.t
    pmtrdifel.r
    @48
    pmtrdifwrdellem3
    adantl
    @37
    @40
    vi
    @17
    r19.26
    sylanbrc
    @19
    @34
    @42
    wa
    vu
    @31
    @20
    @3
    @31
    wceq
    #
    @5
    @34
    @18
    @42
    @51
    @4
    @33
    @2
    @3
    @31
    chash
    fveq2
    eqeq2d
    @51
    @16
    @41
    vi
    @17
    @51
    @9
    @37
    @15
    @40
    @51
    @8
    @36
    cK
    @51
    cK
    @7
    @35
    @6
    @3
    @31
    fveq1
    #
    fveq1d
    eqeq1d
    @51
    @13
    @39
    vx
    @14
    @51
    @12
    @38
    @11
    @51
    @10
    @7
    @35
    @52
    fveq1d
    eqeq2d
    ralbidv
    anbi12d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    ralrimiva
end

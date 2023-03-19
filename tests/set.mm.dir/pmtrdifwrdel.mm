include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "cword.mm"
include "wrex.mm"
include "wcel.mm"
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
include "pmtrdifwrdellem2.mm"
include "pmtrdifwrdellem3.mm"
include "eqeq2d.mm"
include "fveq1.mm"
include "fveq1d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rgen.mm"

theorem pmtrdifwrdel
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
  assert |- A. w e. Word T E. u e. Word R ( ( # ` w ) = ( # ` u ) /\ A. i e. ( 0 ..^ ( # ` w ) ) A. x e. ( N \ { K } ) ( ( w ` i ) ` x ) = ( ( u ` i ) ` x ) )

  proof
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
    vx
    cv
    #
    vi
    cv
    #
    @0
    cfv
    cfv
    #
    @5
    @6
    @2
    cfv
    #
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
    vi
    cc0
    @1
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
    @17
    wcel
    vj
    @12
    vj
    cv
    #
    @0
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
    @15
    wcel
    @1
    @24
    chash
    cfv
    #
    wceq
    #
    @7
    @5
    @6
    @24
    cfv
    #
    cfv
    #
    wceq
    #
    vx
    @11
    wral
    vi
    @12
    wral
    #
    @16
    vn
    cR
    cT
    @24
    cK
    cN
    @0
    pmtrdifel.t
    pmtrdifel.r
    vj
    vn
    @12
    @23
    vn
    cv
    #
    @0
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    @22
    cfv
    vj
    vn
    weq
    #
    @21
    @34
    @22
    @35
    @20
    @33
    @35
    @19
    @32
    cid
    @18
    @31
    @0
    fveq2
    difeq1d
    dmeqd
    fveq2d
    cbvmptv
    #
    pmtrdifwrdellem1
    vn
    cR
    cT
    @24
    cK
    cN
    @0
    pmtrdifel.t
    pmtrdifel.r
    @36
    pmtrdifwrdellem2
    vn
    cR
    cT
    @24
    vi
    vx
    cK
    cN
    @0
    pmtrdifel.t
    pmtrdifel.r
    @36
    pmtrdifwrdellem3
    @14
    @26
    @30
    wa
    vu
    @24
    @15
    @2
    @24
    wceq
    #
    @4
    @26
    @13
    @30
    @37
    @3
    @25
    @1
    @2
    @24
    chash
    fveq2
    eqeq2d
    @37
    @10
    @29
    vi
    vx
    @12
    @11
    @37
    @9
    @28
    @7
    @37
    @5
    @8
    @27
    @6
    @2
    @24
    fveq1
    fveq1d
    eqeq2d
    2ralbidv
    anbi12d
    rspcev
    syl12anc
    rgen
end

include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "csca.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "ccom.mm"
include "eqid.mm"
include "pwsval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "simpr.mm"
include "fvexd.mm"
include "wf.mm"
include "fconst6g.mm"
include "adantr.mm"
include "prds1.mm"
include "wfn.mm"
include "wceq.mm"
include "c0g.mm"
include "cmgp.mm"
include "crn.mm"
include "wss.mm"
include "fn0g.mm"
include "a1i.mm"
include "fnmgp.mm"
include "ssv.mm"
include "fnco.mm"
include "syl3anc.mm"
include "df-ur.mm"
include "fneq1i.mm"
include "sylibr.mm"
include "elex.mm"
include "fcoconst.mm"
include "syl2anc.mm"
include "sneqi.mm"
include "xpeq2i.mm"
include "syl6eqr.mm"
include "3eqtr2rd.mm"

theorem pws1
  let cR: class R
  let c.1: class .1.
  let cI: class I
  let cV: class V
  let cY: class Y
  assume pws1.y: |- Y = ( R ^s I )
  assume pws1.o: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ I e. V ) -> ( I X. { .1. } ) = ( 1r ` Y ) )

  proof
    cR
    crg
    wcel
    #
    cI
    cV
    wcel
    #
    wa
    #
    cY
    cur
    cfv
    cR
    csca
    cfv
    #
    cI
    cR
    csn
    cxp
    #
    cprds
    co
    #
    cur
    cfv
    cur
    @4
    ccom
    #
    cI
    c.1
    csn
    #
    cxp
    #
    @2
    cY
    @5
    cur
    cR
    @3
    cI
    crg
    cV
    cY
    pws1.y
    @3
    eqid
    pwsval
    fveq2d
    @2
    @4
    @3
    cI
    cvv
    cV
    @5
    @5
    eqid
    @0
    @1
    simpr
    @2
    cR
    csca
    fvexd
    @0
    cI
    crg
    @4
    wf
    @1
    cI
    cR
    crg
    fconst6g
    adantr
    prds1
    @2
    @6
    cI
    cR
    cur
    cfv
    #
    csn
    #
    cxp
    #
    @8
    @2
    cur
    cvv
    wfn
    #
    cR
    cvv
    wcel
    #
    @6
    @11
    wceq
    @2
    c0g
    cmgp
    ccom
    #
    cvv
    wfn
    #
    @12
    @2
    c0g
    cvv
    wfn
    #
    cmgp
    cvv
    wfn
    #
    cmgp
    crn
    #
    cvv
    wss
    #
    @15
    @16
    @2
    fn0g
    a1i
    @17
    @2
    fnmgp
    a1i
    @19
    @2
    @18
    ssv
    a1i
    cvv
    cvv
    c0g
    cmgp
    fnco
    syl3anc
    cvv
    cur
    @14
    df-ur
    fneq1i
    sylibr
    @0
    @13
    @1
    cR
    crg
    elex
    adantr
    cur
    cI
    cvv
    cR
    fcoconst
    syl2anc
    @7
    @10
    cI
    c.1
    @9
    pws1.o
    sneqi
    xpeq2i
    syl6eqr
    3eqtr2rd
end

include "crngo.mm"
include "wcel.mm"
include "crnghom.mm"
include "co.mm"
include "w3a.mm"
include "c1st.mm"
include "cfv.mm"
include "cgr.mm"
include "cghomOLD.mm"
include "wf1.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wb.mm"
include "eqid.mm"
include "rngogrpo.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "rngogrphom.mm"
include "crn.mm"
include "rneqi.mm"
include "eqtri.mm"
include "cgi.mm"
include "fveq2i.mm"
include "grpokerinj.mm"
include "syl3anc.mm"

theorem rngokerinj
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume rngkerinj.1: |- G = ( 1st ` R )
  assume rngkerinj.2: |- X = ran G
  assume rngkerinj.3: |- W = ( GId ` G )
  assume rngkerinj.4: |- J = ( 1st ` S )
  assume rngkerinj.5: |- Y = ran J
  assume rngkerinj.6: |- Z = ( GId ` J )


  assert |- ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngHom S ) ) -> ( F : X -1-1-> Y <-> ( `' F " { Z } ) = { W } ) )

  proof
    cR
    crngo
    wcel
    #
    cS
    crngo
    wcel
    #
    cF
    cR
    cS
    crnghom
    co
    wcel
    #
    w3a
    cR
    c1st
    cfv
    #
    cgr
    wcel
    #
    cS
    c1st
    cfv
    #
    cgr
    wcel
    #
    cF
    @3
    @5
    cghomOLD
    co
    wcel
    cX
    cY
    cF
    wf1
    cF
    ccnv
    cZ
    csn
    cima
    cW
    csn
    wceq
    wb
    @0
    @1
    @4
    @2
    cR
    @3
    @3
    eqid
    #
    rngogrpo
    3ad2ant1
    @1
    @0
    @6
    @2
    cS
    @5
    @5
    eqid
    #
    rngogrpo
    3ad2ant2
    cR
    cS
    cF
    @3
    @5
    @7
    @8
    rngogrphom
    cZ
    cF
    @3
    @5
    cW
    cX
    cY
    cX
    cG
    crn
    @3
    crn
    rngkerinj.2
    cG
    @3
    rngkerinj.1
    rneqi
    eqtri
    cW
    cG
    cgi
    cfv
    @3
    cgi
    cfv
    rngkerinj.3
    cG
    @3
    cgi
    rngkerinj.1
    fveq2i
    eqtri
    cY
    cJ
    crn
    @5
    crn
    rngkerinj.5
    cJ
    @5
    rngkerinj.4
    rneqi
    eqtri
    cZ
    cJ
    cgi
    cfv
    @5
    cgi
    cfv
    rngkerinj.6
    cJ
    @5
    cgi
    rngkerinj.4
    fveq2i
    eqtri
    grpokerinj
    syl3anc
end

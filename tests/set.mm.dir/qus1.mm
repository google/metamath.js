include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cqg.mm"
include "co.mm"
include "cmulr.mm"
include "cbs.mm"
include "cqus.mm"
include "wceq.mm"
include "a1i.mm"
include "eqid.mm"
include "csubg.mm"
include "wer.mm"
include "clidl.mm"
include "coppr.mm"
include "2idlval.mm"
include "elin2.mm"
include "simplbi.mm"
include "lidlsubg.mm"
include "sylan2.mm"
include "eqger.mm"
include "syl.mm"
include "cnsg.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "cabl.mm"
include "ringabl.mm"
include "adantr.mm"
include "ablnsg.mm"
include "eleqtrrd.mm"
include "eqgcpbl.mm"
include "2idlcpbl.mm"
include "simpl.mm"
include "qusring2.mm"

theorem qus1
  let cR: class R
  let cS: class S
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let cX: class X
  assume qusring.u: |- U = ( R /s ( R ~QG S ) )
  assume qusring.i: |- I = ( 2Ideal ` R )
  assume qus1.o: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ S e. I ) -> ( U e. Ring /\ [ .1. ] ( R ~QG S ) = ( 1r ` U ) ) )

  proof
    cR
    crg
    wcel
    #
    cS
    cI
    wcel
    #
    wa
    #
    cR
    cplusg
    cfv
    #
    cR
    cS
    cqg
    co
    #
    cR
    cR
    cmulr
    cfv
    #
    cU
    c.1
    cR
    cbs
    cfv
    #
    vd
    vc
    va
    vb
    cU
    cR
    @4
    cqus
    co
    wceq
    @2
    qusring.u
    a1i
    @6
    @6
    wceq
    @2
    @6
    eqid
    #
    a1i
    @3
    eqid
    #
    @5
    eqid
    #
    qus1.o
    @2
    cS
    cR
    csubg
    cfv
    #
    wcel
    #
    @6
    @4
    wer
    @1
    @0
    cS
    cR
    clidl
    cfv
    #
    wcel
    #
    @11
    @1
    @13
    cS
    cR
    coppr
    cfv
    #
    clidl
    cfv
    #
    wcel
    cS
    @12
    @15
    cI
    cR
    cI
    @12
    @15
    @14
    @12
    eqid
    #
    @14
    eqid
    @15
    eqid
    qusring.i
    2idlval
    elin2
    simplbi
    cR
    @12
    cS
    @16
    lidlsubg
    sylan2
    #
    @4
    cR
    @6
    cS
    @7
    @4
    eqid
    #
    eqger
    syl
    @2
    cS
    cR
    cnsg
    cfv
    #
    wcel
    va
    cv
    #
    vc
    cv
    #
    @4
    wbr
    vb
    cv
    #
    vd
    cv
    #
    @4
    wbr
    wa
    @20
    @22
    @3
    co
    @21
    @23
    @3
    co
    @4
    wbr
    wi
    @2
    cS
    @10
    @19
    @17
    @2
    cR
    cabl
    wcel
    #
    @19
    @10
    wceq
    @0
    @24
    @1
    cR
    ringabl
    adantr
    cR
    ablnsg
    syl
    eleqtrrd
    @20
    @22
    @21
    @23
    @3
    @4
    cR
    @6
    cS
    @7
    @18
    @8
    eqgcpbl
    syl
    @20
    @22
    @21
    @23
    cR
    cS
    @5
    @4
    cI
    @6
    @7
    @18
    qusring.i
    @9
    2idlcpbl
    @0
    @1
    simpl
    qusring2
end

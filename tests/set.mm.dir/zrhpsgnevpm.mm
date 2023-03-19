include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "cevpm.mm"
include "cfv.mm"
include "w3a.mm"
include "ccom.mm"
include "c1.mm"
include "csymg.mm"
include "cbs.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cneg.mm"
include "cpr.mm"
include "cress.mm"
include "co.mm"
include "wf.mm"
include "wceq.mm"
include "cghm.mm"
include "eqid.mm"
include "psgnghm2.mm"
include "ghmf.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "evpmss.mm"
include "sseli.mm"
include "3ad2ant3.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "psgnevpm.mm"
include "3adant1.mm"
include "fveq2d.mm"
include "zrh1.mm"
include "3ad2ant1.mm"
include "3eqtrd.mm"

theorem zrhpsgnevpm
  let cR: class R
  let cS: class S
  let c.1: class .1.
  let cF: class F
  let cN: class N
  let cY: class Y
  assume zrhpsgnevpm.y: |- Y = ( ZRHom ` R )
  assume zrhpsgnevpm.s: |- S = ( pmSgn ` N )
  assume zrhpsgnevpm.o: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ N e. Fin /\ F e. ( pmEven ` N ) ) -> ( ( Y o. S ) ` F ) = .1. )

  proof
    cR
    crg
    wcel
    #
    cN
    cfn
    wcel
    #
    cF
    cN
    cevpm
    cfv
    #
    wcel
    #
    w3a
    #
    cF
    cY
    cS
    ccom
    cfv
    #
    cF
    cS
    cfv
    #
    cY
    cfv
    #
    c1
    cY
    cfv
    #
    c.1
    @4
    cN
    csymg
    cfv
    #
    cbs
    cfv
    #
    ccnfld
    cmgp
    cfv
    c1
    c1
    cneg
    cpr
    cress
    co
    #
    cbs
    cfv
    #
    cS
    wf
    #
    cF
    @10
    wcel
    #
    @5
    @7
    wceq
    @1
    @0
    @13
    @3
    @1
    cS
    @9
    @11
    cghm
    co
    wcel
    @13
    cN
    @9
    @11
    cS
    @9
    eqid
    #
    zrhpsgnevpm.s
    @11
    eqid
    psgnghm2
    @9
    @11
    cS
    @10
    @12
    @10
    eqid
    #
    @12
    eqid
    ghmf
    syl
    3ad2ant2
    @3
    @0
    @14
    @1
    @2
    @10
    cF
    cN
    @10
    @9
    @15
    @16
    evpmss
    sseli
    3ad2ant3
    @10
    @12
    cF
    cY
    cS
    fvco3
    syl2anc
    @4
    @6
    c1
    cY
    @1
    @3
    @6
    c1
    wceq
    @0
    cN
    @10
    @9
    cF
    cS
    @15
    @16
    zrhpsgnevpm.s
    psgnevpm
    3adant1
    fveq2d
    @0
    @1
    @8
    c.1
    wceq
    @3
    cR
    c.1
    cY
    zrhpsgnevpm.y
    zrhpsgnevpm.o
    zrh1
    3ad2ant1
    3eqtrd
end

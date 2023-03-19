include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "cevpm.mm"
include "cfv.mm"
include "cdif.mm"
include "w3a.mm"
include "ccom.mm"
include "c1.mm"
include "cneg.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cpr.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "wf.mm"
include "wceq.mm"
include "csymg.mm"
include "cghm.mm"
include "eqid.mm"
include "psgnghm2.mm"
include "ghmf.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "eldifi.mm"
include "3ad2ant3.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "psgnodpm.mm"
include "3adant1.mm"
include "fveq2d.mm"
include "zring.mm"
include "cminusg.mm"
include "cz.mm"
include "crh.mm"
include "zrhrhm.mm"
include "rhmghm.mm"
include "1z.mm"
include "a1i.mm"
include "zringbas.mm"
include "ghminv.mm"
include "zringinvg.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "zrh1.mm"
include "3eqtr3d.mm"
include "3ad2ant1.mm"
include "3eqtrd.mm"

theorem zrhpsgnodpm
  let cP: class P
  let cR: class R
  let cS: class S
  let c.1: class .1.
  let cF: class F
  let cI: class I
  let cN: class N
  let cY: class Y
  assume zrhpsgnevpm.y: |- Y = ( ZRHom ` R )
  assume zrhpsgnevpm.s: |- S = ( pmSgn ` N )
  assume zrhpsgnevpm.o: |- .1. = ( 1r ` R )
  assume zrhpsgnodpm.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume zrhpsgnodpm.i: |- I = ( invg ` R )


  assert |- ( ( R e. Ring /\ N e. Fin /\ F e. ( P \ ( pmEven ` N ) ) ) -> ( ( Y o. S ) ` F ) = ( I ` .1. ) )

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
    cP
    cN
    cevpm
    cfv
    #
    cdif
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
    cneg
    #
    cY
    cfv
    #
    c.1
    cI
    cfv
    #
    @4
    cP
    ccnfld
    cmgp
    cfv
    c1
    @8
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
    cP
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
    cN
    csymg
    cfv
    #
    @11
    cghm
    co
    wcel
    @13
    cN
    @15
    @11
    cS
    @15
    eqid
    #
    zrhpsgnevpm.s
    @11
    eqid
    psgnghm2
    @15
    @11
    cS
    cP
    @12
    zrhpsgnodpm.p
    @12
    eqid
    ghmf
    syl
    3ad2ant2
    @3
    @0
    @14
    @1
    cF
    cP
    @2
    eldifi
    3ad2ant3
    cP
    @12
    cF
    cY
    cS
    fvco3
    syl2anc
    @4
    @6
    @8
    cY
    @1
    @3
    @6
    @8
    wceq
    @0
    cN
    cP
    @15
    cF
    cS
    @16
    zrhpsgnodpm.p
    zrhpsgnevpm.s
    psgnodpm
    3adant1
    fveq2d
    @0
    @1
    @9
    @10
    wceq
    @3
    @0
    c1
    zring
    cminusg
    cfv
    #
    cfv
    #
    cY
    cfv
    #
    c1
    cY
    cfv
    #
    cI
    cfv
    #
    @9
    @10
    @0
    cY
    zring
    cR
    cghm
    co
    wcel
    #
    c1
    cz
    wcel
    #
    @19
    @21
    wceq
    @0
    cY
    zring
    cR
    crh
    co
    wcel
    @22
    cR
    cY
    zrhpsgnevpm.y
    zrhrhm
    zring
    cR
    cY
    rhmghm
    syl
    @23
    @0
    1z
    a1i
    cz
    zring
    cR
    cY
    @17
    cI
    c1
    zringbas
    @17
    eqid
    zrhpsgnodpm.i
    ghminv
    syl2anc
    @19
    @9
    wceq
    @0
    @18
    @8
    cY
    @8
    @18
    @23
    @8
    @18
    wceq
    1z
    c1
    zringinvg
    ax-mp
    eqcomi
    fveq2i
    a1i
    @0
    @20
    c.1
    cI
    cR
    c.1
    cY
    zrhpsgnevpm.y
    zrhpsgnevpm.o
    zrh1
    fveq2d
    3eqtr3d
    3ad2ant1
    3eqtrd
end

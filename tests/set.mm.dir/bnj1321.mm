include "w-bnj15.mm"
include "wex.mm"
include "wa.mm"
include "wsb.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "weu.mm"
include "simpr.mm"
include "w3a.mm"
include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "wcel.mm"
include "simp1.mm"
include "csn.mm"
include "c-bnj18.mm"
include "cun.mm"
include "simplbi.mm"
include "3ad2ant2.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "wrex.mm"
include "cab.mm"
include "nfab1.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "nfv.mm"
include "nfan.mm"
include "eleq1.mm"
include "dmeq.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "sbie.mm"
include "3ad2ant3.mm"
include "eqid.mm"
include "bnj1326.mm"
include "syl3anc.mm"
include "simprbi.mm"
include "eqtr4d.mm"
include "bnj1322.mm"
include "reseq2d.mm"
include "syl.mm"
include "wrel.mm"
include "releq.mm"
include "bnj66.mm"
include "vtoclga.mm"
include "resdm.mm"
include "3syl.mm"
include "eqtrd.mm"
include "eqeq2.mm"
include "mpbid.mm"
include "3eqtr3d.mm"
include "3expib.mm"
include "alrimivv.mm"
include "adantr.mm"
include "eu2.mm"
include "sylanbrc.mm"

theorem bnj1321
  let wta: wff ta
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cY: class Y
  let vd: setvar d
  let vg: setvar g
  let vz: setvar z
  assume bnj1321.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1321.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1321.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1321.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint B f
  disjoint G d
  disjoint G f
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint A g
  disjoint A z
  disjoint d g
  disjoint d z
  disjoint f g
  disjoint f z
  disjoint g x
  disjoint g z
  disjoint x z
  disjoint B g
  disjoint B z
  disjoint C z
  disjoint G g
  disjoint G z
  disjoint R g
  disjoint Y g
  disjoint Y z
  disjoint g ta
  assert |- ( ( R _FrSe A /\ E. f ta ) -> E! f ta )

  proof
    cA
    cR
    w-bnj15
    #
    wta
    vf
    wex
    #
    wa
    @1
    wta
    wta
    vf
    vg
    wsb
    #
    wa
    vf
    cv
    #
    vg
    cv
    #
    wceq
    #
    wi
    #
    vg
    wal
    vf
    wal
    #
    wta
    vf
    weu
    @0
    @1
    simpr
    @0
    @7
    @1
    @0
    @6
    vf
    vg
    @0
    wta
    @2
    @5
    @0
    wta
    @2
    w3a
    #
    @3
    @3
    cdm
    #
    @4
    cdm
    #
    cin
    #
    cres
    #
    @4
    @11
    cres
    #
    @3
    @4
    @8
    @0
    @3
    cC
    wcel
    #
    @4
    cC
    wcel
    #
    @12
    @13
    wceq
    @0
    wta
    @2
    simp1
    wta
    @0
    @14
    @2
    wta
    @14
    @9
    vx
    cv
    #
    csn
    cA
    cR
    @16
    c-bnj18
    cun
    #
    wceq
    #
    bnj1321.4
    simplbi
    3ad2ant2
    #
    @2
    @0
    @15
    wta
    @2
    @15
    @10
    @17
    wceq
    #
    wta
    @15
    @20
    wa
    #
    vf
    vg
    @15
    @20
    vf
    vf
    vg
    cC
    vf
    cC
    @3
    vd
    cv
    #
    wfn
    @16
    @3
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @22
    wral
    wa
    vd
    cB
    wrex
    #
    vf
    cab
    bnj1321.3
    @23
    vf
    nfab1
    nfcxfr
    nfcri
    @20
    vf
    nfv
    nfan
    wta
    @14
    @18
    wa
    @5
    @21
    bnj1321.4
    @5
    @14
    @15
    @18
    @20
    @3
    @4
    cC
    eleq1
    @5
    @9
    @10
    @17
    @3
    @4
    dmeq
    eqeq1d
    anbi12d
    syl5bb
    sbie
    #
    simplbi
    3ad2ant3
    #
    vx
    cA
    cB
    cC
    @11
    cR
    vf
    vf
    vg
    cG
    cY
    vd
    bnj1321.1
    bnj1321.2
    bnj1321.3
    @11
    eqid
    bnj1326
    syl3anc
    @8
    @12
    @3
    @9
    cres
    #
    @3
    @8
    @9
    @10
    wceq
    #
    @12
    @26
    wceq
    @8
    @9
    @17
    @10
    wta
    @0
    @18
    @2
    wta
    @14
    @18
    bnj1321.4
    simprbi
    3ad2ant2
    @2
    @0
    @20
    wta
    @2
    @15
    @20
    @24
    simprbi
    3ad2ant3
    eqtr4d
    #
    @27
    @11
    @9
    @3
    @9
    @10
    bnj1322
    #
    reseq2d
    syl
    @8
    @14
    @3
    wrel
    #
    @26
    @3
    wceq
    @19
    vz
    cv
    #
    wrel
    @30
    vz
    @3
    cC
    @31
    @3
    releq
    vx
    cA
    cB
    cC
    cR
    vf
    vz
    cG
    cY
    vd
    bnj1321.1
    bnj1321.2
    bnj1321.3
    bnj66
    vtoclga
    @3
    resdm
    3syl
    eqtrd
    @8
    @13
    @4
    @10
    cres
    #
    @4
    @8
    @27
    @13
    @32
    wceq
    @28
    @27
    @11
    @10
    @4
    @27
    @11
    @9
    wceq
    @11
    @10
    wceq
    @29
    @9
    @10
    @11
    eqeq2
    mpbid
    reseq2d
    syl
    @8
    @15
    @4
    wrel
    @32
    @4
    wceq
    @25
    vx
    cA
    cB
    cC
    cR
    vf
    vg
    cG
    cY
    vd
    bnj1321.1
    bnj1321.2
    bnj1321.3
    bnj66
    @4
    resdm
    3syl
    eqtrd
    3eqtr3d
    3expib
    alrimivv
    adantr
    wta
    vf
    vg
    wta
    vg
    nfv
    eu2
    sylanbrc
end

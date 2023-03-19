include "wcel.mm"
include "wa.mm"
include "csubgr.mm"
include "wbr.mm"
include "cvtx.mm"
include "cfv.mm"
include "wss.mm"
include "ciedg.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "cedg.mm"
include "cpw.mm"
include "w3a.mm"
include "wb.mm"
include "cv.mm"
include "fveq2.mm"
include "adantr.mm"
include "adantl.mm"
include "sseq12d.mm"
include "dmeqd.mm"
include "reseq12d.mm"
include "eqeq12d.mm"
include "pweqd.mm"
include "3anbi123d.mm"
include "df-subgr.mm"
include "brabga.mm"
include "ancoms.mm"
include "sseq12i.mm"
include "dmeqi.mm"
include "reseq12i.mm"
include "eqeq12i.mm"
include "pweqi.mm"
include "3anbi123i.mm"
include "syl6bbr.mm"

theorem issubgr
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vg: setvar g
  assume issubgr.v: |- V = ( Vtx ` S )
  assume issubgr.a: |- A = ( Vtx ` G )
  assume issubgr.i: |- I = ( iEdg ` S )
  assume issubgr.b: |- B = ( iEdg ` G )
  assume issubgr.e: |- E = ( Edg ` S )


  assert |- ( ( G e. W /\ S e. U ) -> ( S SubGraph G <-> ( V C_ A /\ I = ( B |` dom I ) /\ E C_ ~P V ) ) )

  proof
    cG
    cW
    wcel
    #
    cS
    cU
    wcel
    #
    wa
    cS
    cG
    csubgr
    wbr
    #
    cS
    cvtx
    cfv
    #
    cG
    cvtx
    cfv
    #
    wss
    #
    cS
    ciedg
    cfv
    #
    cG
    ciedg
    cfv
    #
    @6
    cdm
    #
    cres
    #
    wceq
    #
    cS
    cedg
    cfv
    #
    @3
    cpw
    #
    wss
    #
    w3a
    #
    cV
    cA
    wss
    #
    cI
    cB
    cI
    cdm
    #
    cres
    #
    wceq
    #
    cE
    cV
    cpw
    #
    wss
    #
    w3a
    @1
    @0
    @2
    @14
    wb
    vs
    cv
    #
    cvtx
    cfv
    #
    vg
    cv
    #
    cvtx
    cfv
    #
    wss
    #
    @21
    ciedg
    cfv
    #
    @23
    ciedg
    cfv
    #
    @26
    cdm
    #
    cres
    #
    wceq
    #
    @21
    cedg
    cfv
    #
    @22
    cpw
    #
    wss
    #
    w3a
    @14
    vs
    vg
    cS
    cG
    csubgr
    cU
    cW
    @21
    cS
    wceq
    #
    @23
    cG
    wceq
    #
    wa
    #
    @25
    @5
    @30
    @10
    @33
    @13
    @36
    @22
    @3
    @24
    @4
    @34
    @22
    @3
    wceq
    @35
    @21
    cS
    cvtx
    fveq2
    #
    adantr
    @35
    @24
    @4
    wceq
    @34
    @23
    cG
    cvtx
    fveq2
    adantl
    sseq12d
    @36
    @26
    @6
    @29
    @9
    @34
    @26
    @6
    wceq
    @35
    @21
    cS
    ciedg
    fveq2
    #
    adantr
    @36
    @27
    @7
    @28
    @8
    @35
    @27
    @7
    wceq
    @34
    @23
    cG
    ciedg
    fveq2
    adantl
    @34
    @28
    @8
    wceq
    @35
    @34
    @26
    @6
    @38
    dmeqd
    adantr
    reseq12d
    eqeq12d
    @34
    @33
    @13
    wb
    @35
    @34
    @31
    @11
    @32
    @12
    @21
    cS
    cedg
    fveq2
    @34
    @22
    @3
    @37
    pweqd
    sseq12d
    adantr
    3anbi123d
    vg
    vs
    df-subgr
    brabga
    ancoms
    @15
    @5
    @18
    @10
    @20
    @13
    cV
    @3
    cA
    @4
    issubgr.v
    issubgr.a
    sseq12i
    cI
    @6
    @17
    @9
    issubgr.i
    cB
    @7
    @16
    @8
    issubgr.b
    cI
    @6
    issubgr.i
    dmeqi
    reseq12i
    eqeq12i
    cE
    @11
    @19
    @12
    issubgr.e
    cV
    @3
    issubgr.v
    pweqi
    sseq12i
    3anbi123i
    syl6bbr
end

include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "cedg.mm"
include "wbr.mm"
include "ciedg.mm"
include "wfun.mm"
include "w3a.mm"
include "cumgr.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "wss.mm"
include "wi.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "isausgr.mm"
include "mp2an.mm"
include "crn.mm"
include "edgval.mm"
include "a1i.mm"
include "sseq1d.mm"
include "wfn.mm"
include "funfn.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "simp2.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "3exp.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "3imp.mm"
include "eqid.mm"
include "isumgrs.mm"
include "3ad2ant1.mm"
include "mpbird.mm"

theorem ausgrumgri
  let vx: setvar x
  let vv: setvar v
  let ve: setvar e
  let cG: class G
  let cH: class H
  let cW: class W
  let cE: class E
  let cV: class V
  let cX: class X
  let cY: class Y
  assume ausgr.1: |- G = { <. v , e >. | e C_ { x e. ~P v | ( # ` x ) = 2 } }

  disjoint e v
  disjoint e x
  disjoint v x
  disjoint H e
  disjoint H v
  disjoint H x
  disjoint E e
  disjoint E v
  disjoint E x
  disjoint V e
  disjoint V v
  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- ( ( H e. W /\ ( Vtx ` H ) G ( Edg ` H ) /\ Fun ( iEdg ` H ) ) -> H e. UMGraph )

  proof
    cH
    cW
    wcel
    #
    cH
    cvtx
    cfv
    #
    cH
    cedg
    cfv
    #
    cG
    wbr
    #
    cH
    ciedg
    cfv
    #
    wfun
    #
    w3a
    cH
    cumgr
    wcel
    #
    @4
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    @1
    cpw
    crab
    #
    @4
    wf
    #
    @0
    @3
    @5
    @9
    @3
    @2
    @8
    wss
    #
    @0
    @5
    @9
    wi
    #
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @3
    @10
    wb
    cH
    cvtx
    fvex
    cH
    cedg
    fvex
    vx
    vv
    ve
    @2
    cG
    @1
    cvv
    cvv
    ausgr.1
    isausgr
    mp2an
    @0
    @10
    @4
    crn
    #
    @8
    wss
    #
    @11
    @0
    @2
    @12
    @8
    @2
    @12
    wceq
    @0
    cH
    edgval
    a1i
    sseq1d
    @0
    @13
    @5
    @9
    @0
    @13
    @5
    w3a
    @4
    @7
    wfn
    #
    @13
    @9
    @5
    @0
    @14
    @13
    @5
    @14
    @4
    funfn
    biimpi
    3ad2ant3
    @0
    @13
    @5
    simp2
    @7
    @8
    @4
    df-f
    sylanbrc
    3exp
    sylbid
    syl5bi
    3imp
    @0
    @3
    @6
    @9
    wb
    @5
    vx
    cW
    @4
    cH
    @1
    @1
    eqid
    @4
    eqid
    isumgrs
    3ad2ant1
    mpbird
end

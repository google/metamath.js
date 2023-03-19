include "wcel.mm"
include "cnx.mm"
include "cedgf.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "ciedg.mm"
include "c0.mm"
include "wceq.mm"
include "cbs.mm"
include "cop.mm"
include "cstr.mm"
include "wbr.mm"
include "wa.mm"
include "2strstr1.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "c2.mm"
include "cdm.mm"
include "chash.mm"
include "cle.mm"
include "structn0fun.mm"
include "structvtxvallem.mm"
include "funiedgdmge2val.mm"
include "syl2an.mm"
include "mpan.mm"
include "3adant3.mm"
include "cpr.mm"
include "cvv.mm"
include "prex.mm"
include "a1i.mm"
include "syl5eqel.mm"
include "edgfndxid.mm"
include "mp2b.mm"
include "wn.mm"
include "wo.mm"
include "slotsbaseefdif.mm"
include "nesymi.mm"
include "neneq.mm"
include "eqcom.mm"
include "sylnibr.mm"
include "3ad2ant3.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "fvex.mm"
include "elpr.mm"
include "dmeqi.mm"
include "dmpropg.mm"
include "syl5eq.mm"
include "neleqtrrd.mm"
include "ndmfv.mm"
include "syl.mm"
include "eqtrd.mm"

theorem structiedg0val
  let cS: class S
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  assume structvtxvallem.s: |- S e. NN
  assume structvtxvallem.b: |- ( Base ` ndx ) < S
  assume structvtxvallem.g: |- G = { <. ( Base ` ndx ) , V >. , <. S , E >. }


  assert |- ( ( V e. X /\ E e. Y /\ S =/= ( .ef ` ndx ) ) -> ( iEdg ` G ) = (/) )

  proof
    cV
    cX
    wcel
    #
    cE
    cY
    wcel
    #
    cS
    cnx
    cedgf
    cfv
    #
    wne
    #
    w3a
    #
    cG
    ciedg
    cfv
    #
    cG
    cedgf
    cfv
    #
    c0
    @0
    @1
    @5
    @6
    wceq
    #
    @3
    cG
    cnx
    cbs
    cfv
    #
    cS
    cop
    #
    cstr
    wbr
    #
    @0
    @1
    wa
    #
    @7
    cV
    cE
    cG
    cS
    structvtxvallem.g
    structvtxvallem.b
    structvtxvallem.s
    2strstr1
    @10
    cG
    c0
    csn
    cdif
    wfun
    c2
    cG
    cdm
    #
    chash
    cfv
    cle
    wbr
    @7
    @11
    cG
    @9
    structn0fun
    cS
    cE
    cG
    cV
    cX
    cY
    structvtxvallem.s
    structvtxvallem.b
    structvtxvallem.g
    structvtxvallem
    cG
    funiedgdmge2val
    syl2an
    mpan
    3adant3
    @4
    @6
    @2
    cG
    cfv
    #
    c0
    cG
    @8
    cV
    cop
    #
    cS
    cE
    cop
    #
    cpr
    #
    wceq
    #
    cG
    cvv
    wcel
    @6
    @13
    wceq
    structvtxvallem.g
    @17
    cG
    @16
    cvv
    structvtxvallem.g
    @16
    cvv
    wcel
    @17
    @14
    @15
    prex
    a1i
    syl5eqel
    cG
    cvv
    edgfndxid
    mp2b
    @4
    @2
    @12
    wcel
    wn
    @13
    c0
    wceq
    @4
    @12
    @8
    cS
    cpr
    #
    @2
    @4
    @2
    @8
    wceq
    #
    @2
    cS
    wceq
    #
    wo
    #
    @2
    @18
    wcel
    @4
    @19
    wn
    #
    @20
    wn
    #
    @21
    wn
    @22
    @4
    @8
    @2
    slotsbaseefdif
    nesymi
    a1i
    @3
    @0
    @23
    @1
    @3
    cS
    @2
    wceq
    @20
    cS
    @2
    neneq
    @2
    cS
    eqcom
    sylnibr
    3ad2ant3
    @19
    @20
    ioran
    sylanbrc
    @2
    @8
    cS
    cnx
    cedgf
    fvex
    elpr
    sylnibr
    @4
    @12
    @16
    cdm
    #
    @18
    cG
    @16
    structvtxvallem.g
    dmeqi
    @0
    @1
    @24
    @18
    wceq
    @3
    @8
    cV
    cS
    cE
    cX
    cY
    dmpropg
    3adant3
    syl5eq
    neleqtrrd
    @2
    cG
    ndmfv
    syl
    syl5eq
    eqtrd
end

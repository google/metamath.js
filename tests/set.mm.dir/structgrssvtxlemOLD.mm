include "cdm.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "dmexg.mm"
include "syl.mm"
include "cnx.mm"
include "cbs.mm"
include "cedgf.mm"
include "cpr.mm"
include "wss.mm"
include "cop.mm"
include "wceq.mm"
include "dmpropg.mm"
include "syl2anc.mm"
include "dmss.mm"
include "eqsstr3d.mm"
include "wa.mm"
include "fvex.mm"
include "prss.mm"
include "wi.mm"
include "slotsbaseefdif.mm"
include "neeq1.mm"
include "neeq2.mm"
include "rspc2ev.mm"
include "mp3an3.mm"
include "a1i.mm"
include "syl5bir.mm"
include "mpd.mm"
include "hashge2el2difr.mm"

theorem structgrssvtxlemOLD
  let wph: wff ph
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  assume structgrssvtxOLD.g: |- ( ph -> G e. X )
  assume structgrssvtxOLD.f: |- ( ph -> Fun G )
  assume structgrssvtxOLD.v: |- ( ph -> V e. Y )
  assume structgrssvtxOLD.e: |- ( ph -> E e. Z )
  assume structgrssvtxOLD.s: |- ( ph -> { <. ( Base ` ndx ) , V >. , <. ( .ef ` ndx ) , E >. } C_ G )


  assert |- ( ph -> 2 <_ ( # ` dom G ) )

  proof
    wph
    cG
    cdm
    #
    cvv
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    vb
    @0
    wrex
    va
    @0
    wrex
    #
    c2
    @0
    chash
    cfv
    cle
    wbr
    wph
    cG
    cX
    wcel
    @1
    structgrssvtxOLD.g
    cG
    cX
    dmexg
    syl
    wph
    cnx
    cbs
    cfv
    #
    cnx
    cedgf
    cfv
    #
    cpr
    #
    @0
    wss
    #
    @5
    wph
    @8
    @6
    cV
    cop
    @7
    cE
    cop
    cpr
    #
    cdm
    #
    @0
    wph
    cV
    cY
    wcel
    cE
    cZ
    wcel
    @11
    @8
    wceq
    structgrssvtxOLD.v
    structgrssvtxOLD.e
    @6
    cV
    @7
    cE
    cY
    cZ
    dmpropg
    syl2anc
    wph
    @10
    cG
    wss
    @11
    @0
    wss
    structgrssvtxOLD.s
    @10
    cG
    dmss
    syl
    eqsstr3d
    @9
    @6
    @0
    wcel
    #
    @7
    @0
    wcel
    #
    wa
    #
    wph
    @5
    @6
    @7
    @0
    cnx
    cbs
    fvex
    cnx
    cedgf
    fvex
    prss
    @14
    @5
    wi
    wph
    @12
    @13
    @6
    @7
    wne
    #
    @5
    slotsbaseefdif
    @4
    @15
    @6
    @3
    wne
    va
    vb
    @6
    @7
    @0
    @0
    @2
    @6
    @3
    neeq1
    @3
    @7
    @6
    neeq2
    rspc2ev
    mp3an3
    a1i
    syl5bir
    mpd
    va
    vb
    @0
    cvv
    hashge2el2difr
    syl2anc
end

include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "cres.mm"
include "cdm.mm"
include "wf1o.mm"
include "wf1.mm"
include "wss.mm"
include "ctrls.mm"
include "wbr.mm"
include "trlf1.mm"
include "syl.mm"
include "wcel.mm"
include "cuz.mm"
include "elfzouz2.mm"
include "fzoss2.mm"
include "3syl.mm"
include "f1ores.mm"
include "syl2anc.mm"
include "wceq.mm"
include "a1i.mm"
include "fveq2i.mm"
include "cword.mm"
include "cfz.mm"
include "cwlks.mm"
include "trliswlk.mm"
include "wlkf.mm"
include "elfzofz.mm"
include "wlkreslem0.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "wf.mm"
include "wrdf.mm"
include "fimass.mm"
include "ssdmres.mm"
include "sylib.mm"
include "f1oeq123d.mm"
include "mpbird.mm"

theorem trlreslem
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  assume trlres.v: |- V = ( Vtx ` G )
  assume trlres.i: |- I = ( iEdg ` G )
  assume trlres.d: |- ( ph -> F ( Trails ` G ) P )
  assume trlres.n: |- ( ph -> N e. ( 0 ..^ ( # ` F ) ) )
  assume trlres.h: |- H = ( F |` ( 0 ..^ N ) )


  assert |- ( ph -> H : ( 0 ..^ ( # ` H ) ) -1-1-onto-> dom ( I |` ( F " ( 0 ..^ N ) ) ) )

  proof
    wph
    cc0
    cH
    chash
    cfv
    #
    cfzo
    co
    #
    cI
    cF
    cc0
    cN
    cfzo
    co
    #
    cima
    #
    cres
    cdm
    #
    cH
    wf1o
    @2
    @3
    cF
    @2
    cres
    #
    wf1o
    #
    wph
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cI
    cdm
    #
    cF
    wf1
    #
    @2
    @8
    wss
    #
    @6
    wph
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    @10
    trlres.d
    cP
    cF
    cG
    cI
    trlres.i
    trlf1
    syl
    wph
    cN
    @8
    wcel
    #
    @7
    cN
    cuz
    cfv
    wcel
    @11
    trlres.n
    cN
    cc0
    @7
    elfzouz2
    cN
    cc0
    @7
    fzoss2
    3syl
    @8
    @9
    @2
    cF
    f1ores
    syl2anc
    wph
    @1
    @2
    @4
    @3
    cH
    @5
    cH
    @5
    wceq
    wph
    trlres.h
    a1i
    wph
    @0
    cN
    cc0
    cfzo
    wph
    @0
    @5
    chash
    cfv
    #
    cN
    cH
    @5
    chash
    trlres.h
    fveq2i
    wph
    cF
    @9
    cword
    wcel
    #
    cN
    cc0
    @7
    cfz
    co
    wcel
    #
    @14
    cN
    wceq
    wph
    @12
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @15
    trlres.d
    cP
    cF
    cG
    trliswlk
    #
    cP
    cF
    cG
    cI
    trlres.i
    wlkf
    #
    3syl
    wph
    @13
    @16
    trlres.n
    cN
    cc0
    @7
    elfzofz
    syl
    @9
    cF
    cN
    wlkreslem0
    syl2anc
    syl5eq
    oveq2d
    wph
    @3
    @9
    wss
    #
    @4
    @3
    wceq
    wph
    @12
    @17
    @20
    trlres.d
    @18
    @17
    @15
    @8
    @9
    cF
    wf
    @20
    @19
    @9
    cF
    wrdf
    @8
    @9
    cF
    @2
    fimass
    3syl
    3syl
    @3
    cI
    ssdmres
    sylib
    f1oeq123d
    mpbird
end

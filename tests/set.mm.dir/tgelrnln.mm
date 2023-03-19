include "co.mm"
include "cop.mm"
include "cfv.mm"
include "crn.mm"
include "df-ov.mm"
include "cxp.mm"
include "cid.mm"
include "cdif.mm"
include "wfn.mm"
include "wcel.mm"
include "cstrkg.mm"
include "tglnfn.mm"
include "syl.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "wne.mm"
include "wn.mm"
include "wbr.mm"
include "wceq.mm"
include "df-br.mm"
include "ideqg.mm"
include "syl5bbr.mm"
include "necon3bbid.mm"
include "biimpar.mm"
include "eldifd.mm"
include "fnfvelrn.mm"
include "syl5eqel.mm"

theorem tgelrnln
  let wph: wff ph
  let cB: class B
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  assume tglineelsb2.p: |- B = ( Base ` G )
  assume tglineelsb2.i: |- I = ( Itv ` G )
  assume tglineelsb2.l: |- L = ( LineG ` G )
  assume tglineelsb2.g: |- ( ph -> G e. TarskiG )
  assume tgelrnln.x: |- ( ph -> X e. B )
  assume tgelrnln.y: |- ( ph -> Y e. B )
  assume tgelrnln.d: |- ( ph -> X =/= Y )


  assert |- ( ph -> ( X L Y ) e. ran L )

  proof
    wph
    cX
    cY
    cL
    co
    cX
    cY
    cop
    #
    cL
    cfv
    #
    cL
    crn
    #
    cX
    cY
    cL
    df-ov
    wph
    cL
    cB
    cB
    cxp
    #
    cid
    cdif
    #
    wfn
    #
    @0
    @4
    wcel
    @1
    @2
    wcel
    wph
    cG
    cstrkg
    wcel
    @5
    tglineelsb2.g
    cB
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.l
    tglineelsb2.i
    tglnfn
    syl
    wph
    @0
    @3
    cid
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    #
    @0
    @3
    wcel
    tgelrnln.x
    tgelrnln.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    wph
    @6
    cX
    cY
    wne
    #
    @0
    cid
    wcel
    #
    wn
    #
    tgelrnln.y
    tgelrnln.d
    @6
    @9
    @7
    @6
    @8
    cX
    cY
    @8
    cX
    cY
    cid
    wbr
    @6
    cX
    cY
    wceq
    cX
    cY
    cid
    df-br
    cX
    cY
    cB
    ideqg
    syl5bbr
    necon3bbid
    biimpar
    syl2anc
    eldifd
    @4
    @0
    cL
    fnfvelrn
    syl2anc
    syl5eqel
end

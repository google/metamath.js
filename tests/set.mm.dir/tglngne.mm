include "cop.mm"
include "cid.mm"
include "wcel.mm"
include "wn.mm"
include "wne.mm"
include "cxp.mm"
include "cdm.mm"
include "cdif.mm"
include "cfv.mm"
include "co.mm"
include "df-ov.mm"
include "syl6eleq.mm"
include "elfvdm.mm"
include "syl.mm"
include "cstrkg.mm"
include "wfn.mm"
include "wceq.mm"
include "tglnfn.mm"
include "fndm.mm"
include "3syl.mm"
include "eleqtrd.mm"
include "eldifbd.mm"
include "wbr.mm"
include "df-br.mm"
include "wb.mm"
include "ideqg.mm"
include "syl5bbr.mm"
include "necon3bbid.mm"
include "mpbid.mm"

theorem tglngne
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tglngval.p: |- P = ( Base ` G )
  assume tglngval.l: |- L = ( LineG ` G )
  assume tglngval.i: |- I = ( Itv ` G )
  assume tglngval.g: |- ( ph -> G e. TarskiG )
  assume tglngval.x: |- ( ph -> X e. P )
  assume tglngval.y: |- ( ph -> Y e. P )
  assume tglngne.1: |- ( ph -> Z e. ( X L Y ) )


  assert |- ( ph -> X =/= Y )

  proof
    wph
    cX
    cY
    cop
    #
    cid
    wcel
    #
    wn
    cX
    cY
    wne
    wph
    @0
    cP
    cP
    cxp
    #
    cid
    wph
    @0
    cL
    cdm
    #
    @2
    cid
    cdif
    #
    wph
    cZ
    @0
    cL
    cfv
    #
    wcel
    @0
    @3
    wcel
    wph
    cZ
    cX
    cY
    cL
    co
    @5
    tglngne.1
    cX
    cY
    cL
    df-ov
    syl6eleq
    cZ
    @0
    cL
    elfvdm
    syl
    wph
    cG
    cstrkg
    wcel
    cL
    @4
    wfn
    @3
    @4
    wceq
    tglngval.g
    cP
    cG
    cI
    cL
    tglngval.p
    tglngval.l
    tglngval.i
    tglnfn
    @4
    cL
    fndm
    3syl
    eleqtrd
    eldifbd
    wph
    @1
    cX
    cY
    @1
    cX
    cY
    cid
    wbr
    #
    wph
    cX
    cY
    wceq
    #
    cX
    cY
    cid
    df-br
    wph
    cY
    cP
    wcel
    @6
    @7
    wb
    tglngval.y
    cX
    cY
    cP
    ideqg
    syl
    syl5bbr
    necon3bbid
    mpbid
end

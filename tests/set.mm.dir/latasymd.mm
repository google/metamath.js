include "wbr.mm"
include "wceq.mm"
include "clat.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "latasymb.mm"
include "syl3anc.mm"
include "mpbi2and.mm"

theorem latasymd
  let wph: wff ph
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume latasymd.b: |- B = ( Base ` K )
  assume latasymd.l: |- .<_ = ( le ` K )
  assume latasymd.3: |- ( ph -> K e. Lat )
  assume latasymd.4: |- ( ph -> X e. B )
  assume latasymd.5: |- ( ph -> Y e. B )
  assume latasymd.6: |- ( ph -> X .<_ Y )
  assume latasymd.7: |- ( ph -> Y .<_ X )


  assert |- ( ph -> X = Y )

  proof
    wph
    cX
    cY
    c.le
    wbr
    #
    cY
    cX
    c.le
    wbr
    #
    cX
    cY
    wceq
    #
    latasymd.6
    latasymd.7
    wph
    cK
    clat
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    @0
    @1
    wa
    @2
    wb
    latasymd.3
    latasymd.4
    latasymd.5
    cB
    cK
    c.le
    cX
    cY
    latasymd.b
    latasymd.l
    latasymb
    syl3anc
    mpbi2and
end

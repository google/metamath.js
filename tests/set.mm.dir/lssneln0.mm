include "wcel.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wceq.mm"
include "wi.mm"
include "clmod.mm"
include "lss0cl.mm"
include "syl2anc.mm"
include "eleq1a.mm"
include "syl.mm"
include "necon3bd.mm"
include "mpd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"

theorem lssneln0
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lssneln0.v: |- V = ( Base ` W )
  assume lssneln0.o: |- .0. = ( 0g ` W )
  assume lssneln0.s: |- S = ( LSubSp ` W )
  assume lssneln0.w: |- ( ph -> W e. LMod )
  assume lssneln0.u: |- ( ph -> U e. S )
  assume lssneln0.x: |- ( ph -> X e. V )
  assume lssneln0.n: |- ( ph -> -. X e. U )


  assert |- ( ph -> X e. ( V \ { .0. } ) )

  proof
    wph
    cX
    cV
    wcel
    cX
    c.0
    wne
    #
    cX
    cV
    c.0
    csn
    cdif
    wcel
    lssneln0.x
    wph
    cX
    cU
    wcel
    #
    wn
    @0
    lssneln0.n
    wph
    @1
    cX
    c.0
    wph
    c.0
    cU
    wcel
    #
    cX
    c.0
    wceq
    @1
    wi
    wph
    cW
    clmod
    wcel
    cU
    cS
    wcel
    @2
    lssneln0.w
    lssneln0.u
    cS
    cU
    cW
    c.0
    lssneln0.o
    lssneln0.s
    lss0cl
    syl2anc
    c.0
    cU
    cX
    eleq1a
    syl
    necon3bd
    mpd
    cX
    cV
    c.0
    eldifsn
    sylanbrc
end

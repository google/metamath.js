include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "clvec.mm"
include "wcel.mm"
include "adantr.mm"
include "cdif.mm"
include "simpr.mm"
include "lspabs2.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem lspindp3
  let wph: wff ph
  let c.pl: class .+
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lspindp3.v: |- V = ( Base ` W )
  assume lspindp3.p: |- .+ = ( +g ` W )
  assume lspindp3.o: |- .0. = ( 0g ` W )
  assume lspindp3.n: |- N = ( LSpan ` W )
  assume lspindp3.w: |- ( ph -> W e. LVec )
  assume lspindp3.x: |- ( ph -> X e. V )
  assume lspindp3.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lspindp3.e: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )


  assert |- ( ph -> ( N ` { X } ) =/= ( N ` { ( X .+ Y ) } ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    wne
    @0
    cX
    cY
    c.pl
    co
    csn
    cN
    cfv
    #
    wne
    lspindp3.e
    wph
    @0
    @2
    @0
    @1
    wph
    @0
    @2
    wceq
    #
    @0
    @1
    wceq
    wph
    @3
    wa
    c.pl
    cN
    cV
    cW
    cX
    cY
    c.0
    lspindp3.v
    lspindp3.p
    lspindp3.o
    lspindp3.n
    wph
    cW
    clvec
    wcel
    @3
    lspindp3.w
    adantr
    wph
    cX
    cV
    wcel
    @3
    lspindp3.x
    adantr
    wph
    cY
    cV
    c.0
    csn
    cdif
    wcel
    @3
    lspindp3.y
    adantr
    wph
    @3
    simpr
    lspabs2
    ex
    necon3d
    mpd
end

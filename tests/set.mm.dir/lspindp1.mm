include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "cpr.mm"
include "wcel.mm"
include "wn.mm"
include "eldifad.mm"
include "lspindpi.mm"
include "simprd.mm"
include "wa.mm"
include "clvec.mm"
include "adantr.mm"
include "cdif.mm"
include "simpr.mm"
include "lspexch.mm"
include "mtand.mm"
include "jca.mm"

theorem lspindp1
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume lspindp1.v: |- V = ( Base ` W )
  assume lspindp1.o: |- .0. = ( 0g ` W )
  assume lspindp1.n: |- N = ( LSpan ` W )
  assume lspindp1.w: |- ( ph -> W e. LVec )
  assume lspindp1.y: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lspindp1.z: |- ( ph -> Y e. V )
  assume lspindp1.x: |- ( ph -> Z e. V )
  assume lspindp1.q: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume lspindp1.e: |- ( ph -> -. Z e. ( N ` { X , Y } ) )


  assert |- ( ph -> ( ( N ` { Z } ) =/= ( N ` { Y } ) /\ -. X e. ( N ` { Z , Y } ) ) )

  proof
    wph
    cZ
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
    #
    cX
    cZ
    cY
    cpr
    cN
    cfv
    wcel
    #
    wn
    wph
    @0
    cX
    csn
    cN
    cfv
    #
    wne
    @2
    wph
    cN
    cV
    cW
    cZ
    cX
    cY
    lspindp1.v
    lspindp1.n
    lspindp1.w
    lspindp1.x
    wph
    cX
    cV
    c.0
    csn
    #
    lspindp1.y
    eldifad
    lspindp1.z
    lspindp1.e
    lspindpi
    simprd
    wph
    @3
    cZ
    cX
    cY
    cpr
    cN
    cfv
    wcel
    lspindp1.e
    wph
    @3
    wa
    cN
    cV
    cW
    cX
    cZ
    c.0
    cY
    lspindp1.v
    lspindp1.o
    lspindp1.n
    wph
    cW
    clvec
    wcel
    @3
    lspindp1.w
    adantr
    wph
    cX
    cV
    @5
    cdif
    wcel
    @3
    lspindp1.y
    adantr
    wph
    cZ
    cV
    wcel
    @3
    lspindp1.x
    adantr
    wph
    cY
    cV
    wcel
    @3
    lspindp1.z
    adantr
    wph
    @4
    @1
    wne
    @3
    lspindp1.q
    adantr
    wph
    @3
    simpr
    lspexch
    mtand
    jca
end

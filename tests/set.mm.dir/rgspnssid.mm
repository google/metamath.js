include "cv.mm"
include "wss.mm"
include "csubrg.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "ssintub.mm"
include "rgspnval.mm"
include "syl5sseqr.mm"

theorem rgspnssid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let cS: class S
  assume rgspnval.r: |- ( ph -> R e. Ring )
  assume rgspnval.b: |- ( ph -> B = ( Base ` R ) )
  assume rgspnval.ss: |- ( ph -> A C_ B )
  assume rgspnval.n: |- ( ph -> N = ( RingSpan ` R ) )
  assume rgspnval.sp: |- ( ph -> U = ( N ` A ) )


  assert |- ( ph -> A C_ U )

  proof
    wph
    cA
    vt
    cv
    wss
    vt
    cR
    csubrg
    cfv
    #
    crab
    cint
    cA
    cU
    vt
    cA
    @0
    ssintub
    wph
    vt
    cA
    cB
    cR
    cU
    cN
    rgspnval.r
    rgspnval.b
    rgspnval.ss
    rgspnval.n
    rgspnval.sp
    rgspnval
    syl5sseqr
end

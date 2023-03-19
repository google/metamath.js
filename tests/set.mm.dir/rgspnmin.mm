include "cv.mm"
include "wss.mm"
include "csubrg.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "rgspnval.mm"
include "wcel.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "intss1.mm"
include "syl.mm"
include "eqsstrd.mm"

theorem rgspnmin
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cU: class U
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  assume rgspnval.r: |- ( ph -> R e. Ring )
  assume rgspnval.b: |- ( ph -> B = ( Base ` R ) )
  assume rgspnval.ss: |- ( ph -> A C_ B )
  assume rgspnval.n: |- ( ph -> N = ( RingSpan ` R ) )
  assume rgspnval.sp: |- ( ph -> U = ( N ` A ) )
  assume rgspnmin.sr: |- ( ph -> S e. ( SubRing ` R ) )
  assume rgspnmin.ss: |- ( ph -> A C_ S )


  assert |- ( ph -> U C_ S )

  proof
    wph
    cU
    cA
    vt
    cv
    #
    wss
    #
    vt
    cR
    csubrg
    cfv
    #
    crab
    #
    cint
    #
    cS
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
    wph
    cS
    @3
    wcel
    #
    @4
    cS
    wss
    wph
    cS
    @2
    wcel
    cA
    cS
    wss
    #
    @5
    rgspnmin.sr
    rgspnmin.ss
    @1
    @6
    vt
    cS
    @2
    @0
    cS
    cA
    sseq2
    elrab
    sylanbrc
    cS
    @3
    intss1
    syl
    eqsstrd
end

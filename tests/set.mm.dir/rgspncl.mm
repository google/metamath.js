include "cv.mm"
include "wss.mm"
include "csubrg.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "rgspnval.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "ssrab2.mm"
include "wrex.mm"
include "cbs.mm"
include "crg.mm"
include "eqid.mm"
include "subrgid.mm"
include "syl.mm"
include "eqeltrd.mm"
include "sseq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rabn0.mm"
include "sylibr.mm"
include "subrgint.mm"
include "sylancr.mm"

theorem rgspncl
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


  assert |- ( ph -> U e. ( SubRing ` R ) )

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
    @2
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
    @3
    @2
    wss
    @3
    c0
    wne
    #
    @4
    @2
    wcel
    @1
    vt
    @2
    ssrab2
    wph
    @1
    vt
    @2
    wrex
    #
    @5
    wph
    cB
    @2
    wcel
    cA
    cB
    wss
    #
    @6
    wph
    cB
    cR
    cbs
    cfv
    #
    @2
    rgspnval.b
    wph
    cR
    crg
    wcel
    @8
    @2
    wcel
    rgspnval.r
    @8
    cR
    @8
    eqid
    subrgid
    syl
    eqeltrd
    rgspnval.ss
    @1
    @7
    vt
    cB
    @2
    @0
    cB
    cA
    sseq2
    rspcev
    syl2anc
    @1
    vt
    @2
    rabn0
    sylibr
    cR
    @3
    subrgint
    sylancr
    eqeltrd
end

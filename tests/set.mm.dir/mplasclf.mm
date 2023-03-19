include "wf.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "eqid.mm"
include "mplring.mm"
include "mpllmod.mm"
include "asclf.mm"
include "syl2anc.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "feq2d.mm"
include "mpbird.mm"

theorem mplasclf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cI: class I
  let cK: class K
  let cW: class W
  assume mplasclf.p: |- P = ( I mPoly R )
  assume mplasclf.b: |- B = ( Base ` P )
  assume mplasclf.k: |- K = ( Base ` R )
  assume mplasclf.a: |- A = ( algSc ` P )
  assume mplasclf.i: |- ( ph -> I e. W )
  assume mplasclf.r: |- ( ph -> R e. Ring )


  assert |- ( ph -> A : K --> B )

  proof
    wph
    cK
    cB
    cA
    wf
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    cB
    cA
    wf
    #
    wph
    cI
    cW
    wcel
    #
    cR
    crg
    wcel
    #
    @2
    mplasclf.i
    mplasclf.r
    @3
    @4
    wa
    cA
    cB
    @0
    @1
    cP
    mplasclf.a
    @0
    eqid
    cP
    cR
    cI
    cW
    mplasclf.p
    mplring
    cP
    cR
    cI
    cW
    mplasclf.p
    mpllmod
    @1
    eqid
    mplasclf.b
    asclf
    syl2anc
    wph
    cK
    @1
    cB
    cA
    wph
    cK
    cR
    cbs
    cfv
    @1
    mplasclf.k
    wph
    cR
    @0
    cbs
    wph
    cP
    cR
    cI
    cW
    crg
    mplasclf.p
    mplasclf.i
    mplasclf.r
    mplsca
    fveq2d
    syl5eq
    feq2d
    mpbird
end

include "cfv.mm"
include "c1st.mm"
include "ccom.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "fveq1i.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "seq1.mm"
include "syl.mm"
include "cuz.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "fvconst2g.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem algr0
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  assume algrf.1: |- Z = ( ZZ>= ` M )
  assume algrf.2: |- R = seq M ( ( F o. 1st ) , ( Z X. { A } ) )
  assume algrf.3: |- ( ph -> M e. ZZ )
  assume algrf.4: |- ( ph -> A e. S )


  assert |- ( ph -> ( R ` M ) = A )

  proof
    wph
    cM
    cR
    cfv
    cM
    cF
    c1st
    ccom
    #
    cZ
    cA
    csn
    cxp
    #
    cM
    cseq
    #
    cfv
    #
    cA
    cM
    cR
    @2
    algrf.2
    fveq1i
    wph
    @3
    cM
    @1
    cfv
    #
    cA
    wph
    cM
    cz
    wcel
    #
    @3
    @4
    wceq
    algrf.3
    @0
    @1
    cM
    seq1
    syl
    wph
    cA
    cS
    wcel
    cM
    cZ
    wcel
    @4
    cA
    wceq
    algrf.4
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    @5
    cM
    @6
    wcel
    algrf.3
    cM
    uzid
    syl
    algrf.1
    syl6eleqr
    cZ
    cA
    cM
    cS
    fvconst2g
    syl2anc
    eqtrd
    syl5eq
end

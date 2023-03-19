include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "wfn.mm"
include "w3a.mm"
include "xpexg.mm"
include "3adant3.mm"
include "syl.mm"
include "simp3d.mm"
include "jca.mm"
include "eqid.mm"
include "frlmbasf.mm"
include "ffn.mm"
include "3syl.mm"
include "3simpa.mm"
include "fnmpt2ovd.mm"

theorem mpt2frlmd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  assume mpt2frlmd.f: |- F = ( R freeLMod ( N X. M ) )
  assume mpt2frlmd.v: |- V = ( Base ` F )
  assume mpt2frlmd.s: |- ( ( i = a /\ j = b ) -> A = B )
  assume mpt2frlmd.a: |- ( ( ph /\ i e. N /\ j e. M ) -> A e. X )
  assume mpt2frlmd.b: |- ( ( ph /\ a e. N /\ b e. M ) -> B e. Y )
  assume mpt2frlmd.e: |- ( ph -> ( N e. U /\ M e. W /\ Z e. V ) )

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint N a
  disjoint N b
  disjoint N i
  disjoint N j
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint M a
  disjoint M b
  disjoint M i
  disjoint M j
  disjoint R a
  disjoint R b
  disjoint R i
  disjoint R j
  disjoint V a
  disjoint V b
  disjoint V i
  disjoint V j
  disjoint U a
  disjoint U b
  disjoint U i
  disjoint U j
  disjoint W a
  disjoint W b
  disjoint W i
  disjoint W j
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint Y a
  disjoint Y b
  disjoint Y i
  disjoint Y j
  disjoint Z a
  disjoint Z b
  disjoint Z i
  disjoint Z j
  disjoint a ph
  disjoint b ph
  disjoint i ph
  disjoint j ph
  assert |- ( ph -> ( Z = ( a e. N , b e. M |-> B ) <-> A. i e. N A. j e. M ( i Z j ) = A ) )

  proof
    wph
    cN
    cM
    cB
    cA
    cX
    vi
    vj
    cZ
    cY
    cU
    cW
    va
    vb
    wph
    cN
    cM
    cxp
    #
    cvv
    wcel
    #
    cZ
    cV
    wcel
    #
    wa
    @0
    cR
    cbs
    cfv
    #
    cZ
    wf
    cZ
    @0
    wfn
    wph
    @1
    @2
    wph
    cN
    cU
    wcel
    #
    cM
    cW
    wcel
    #
    @2
    w3a
    #
    @1
    mpt2frlmd.e
    @4
    @5
    @1
    @2
    cN
    cM
    cU
    cW
    xpexg
    3adant3
    syl
    wph
    @4
    @5
    @2
    mpt2frlmd.e
    simp3d
    jca
    cV
    cR
    cF
    @0
    @3
    cvv
    cZ
    mpt2frlmd.f
    @3
    eqid
    mpt2frlmd.v
    frlmbasf
    @0
    @3
    cZ
    ffn
    3syl
    mpt2frlmd.s
    mpt2frlmd.a
    mpt2frlmd.b
    wph
    @6
    @4
    @5
    wa
    mpt2frlmd.e
    @4
    @5
    @2
    3simpa
    syl
    fnmpt2ovd
end

include "c1.mm"
include "crelexp.mm"
include "co.mm"
include "cv.mm"
include "ciun.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "oveq2.mm"
include "ssiun2s.mm"
include "syl.mm"
include "relexp1d.mm"
include "cvv.mm"
include "wceq.mm"
include "wral.mm"
include "ovex.mm"
include "rgenw.mm"
include "iunexg.mm"
include "sylancl.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "3sstr3d.mm"

theorem fvmptiunrelexplb1d
  let wph: wff ph
  let cC: class C
  let cR: class R
  let vn: setvar n
  let cN: class N
  let vr: setvar r
  assume fvmptiunrelexplb1d.c: |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) )
  assume fvmptiunrelexplb1d.r: |- ( ph -> R e. _V )
  assume fvmptiunrelexplb1d.n: |- ( ph -> N e. _V )
  assume fvmptiunrelexplb1d.1: |- ( ph -> 1 e. N )

  disjoint n r
  disjoint N n
  disjoint N r
  disjoint R n
  disjoint R r
  assert |- ( ph -> R C_ ( C ` R ) )

  proof
    wph
    cR
    c1
    crelexp
    co
    #
    vn
    cN
    cR
    vn
    cv
    #
    crelexp
    co
    #
    ciun
    #
    cR
    cR
    cC
    cfv
    #
    wph
    c1
    cN
    wcel
    @0
    @3
    wss
    fvmptiunrelexplb1d.1
    vn
    cN
    @2
    c1
    @0
    @1
    c1
    cR
    crelexp
    oveq2
    ssiun2s
    syl
    wph
    cR
    fvmptiunrelexplb1d.r
    relexp1d
    wph
    @4
    @3
    wph
    cR
    cvv
    wcel
    @3
    cvv
    wcel
    #
    @4
    @3
    wceq
    fvmptiunrelexplb1d.r
    wph
    cN
    cvv
    wcel
    @2
    cvv
    wcel
    #
    vn
    cN
    wral
    @5
    fvmptiunrelexplb1d.n
    @6
    vn
    cN
    cR
    @1
    crelexp
    ovex
    rgenw
    vn
    cN
    @2
    cvv
    cvv
    iunexg
    sylancl
    vr
    cR
    vn
    cN
    vr
    cv
    #
    @1
    crelexp
    co
    #
    ciun
    @3
    cvv
    cvv
    cC
    @7
    cR
    wceq
    vn
    cN
    @8
    @2
    @7
    cR
    @1
    crelexp
    oveq1
    iuneq2d
    fvmptiunrelexplb1d.c
    fvmptg
    syl2anc
    eqcomd
    3sstr3d
end

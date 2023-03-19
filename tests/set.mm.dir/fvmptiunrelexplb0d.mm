include "cc0.mm"
include "crelexp.mm"
include "co.mm"
include "cv.mm"
include "ciun.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "oveq2.mm"
include "ssiun2s.mm"
include "syl.mm"
include "cvv.mm"
include "wceq.mm"
include "relexp0g.mm"
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

theorem fvmptiunrelexplb0d
  let wph: wff ph
  let cC: class C
  let cR: class R
  let vn: setvar n
  let cN: class N
  let vr: setvar r
  assume fvmptiunrelexplb0d.c: |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) )
  assume fvmptiunrelexplb0d.r: |- ( ph -> R e. _V )
  assume fvmptiunrelexplb0d.n: |- ( ph -> N e. _V )
  assume fvmptiunrelexplb0d.0: |- ( ph -> 0 e. N )

  disjoint n r
  disjoint N n
  disjoint N r
  disjoint R n
  disjoint R r
  assert |- ( ph -> ( _I |` ( dom R u. ran R ) ) C_ ( C ` R ) )

  proof
    wph
    cR
    cc0
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
    cid
    cR
    cdm
    cR
    crn
    cun
    cres
    #
    cR
    cC
    cfv
    #
    wph
    cc0
    cN
    wcel
    @0
    @3
    wss
    fvmptiunrelexplb0d.0
    vn
    cN
    @2
    cc0
    @0
    @1
    cc0
    cR
    crelexp
    oveq2
    ssiun2s
    syl
    wph
    cR
    cvv
    wcel
    #
    @0
    @4
    wceq
    fvmptiunrelexplb0d.r
    cR
    cvv
    relexp0g
    syl
    wph
    @5
    @3
    wph
    @6
    @3
    cvv
    wcel
    #
    @5
    @3
    wceq
    fvmptiunrelexplb0d.r
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
    @7
    fvmptiunrelexplb0d.n
    @8
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
    @9
    cR
    wceq
    vn
    cN
    @10
    @2
    @9
    cR
    @1
    crelexp
    oveq1
    iuneq2d
    fvmptiunrelexplb0d.c
    fvmptg
    syl2anc
    eqcomd
    3sstr3d
end

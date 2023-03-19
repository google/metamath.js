include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cfv.mm"
include "wrel.mm"
include "wceq.mm"
include "relfld.mm"
include "syl.mm"
include "reseq2d.mm"
include "fvmptiunrelexplb0d.mm"
include "eqsstrd.mm"

theorem fvmptiunrelexplb0da
  let wph: wff ph
  let cC: class C
  let cR: class R
  let vn: setvar n
  let cN: class N
  let vr: setvar r
  assume fvmptiunrelexplb0da.c: |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) )
  assume fvmptiunrelexplb0da.r: |- ( ph -> R e. _V )
  assume fvmptiunrelexplb0da.n: |- ( ph -> N e. _V )
  assume fvmptiunrelexplb0da.rel: |- ( ph -> Rel R )
  assume fvmptiunrelexplb0da.0: |- ( ph -> 0 e. N )

  disjoint n r
  disjoint C n
  disjoint N n
  disjoint C r
  disjoint N r
  disjoint C N
  disjoint R n
  disjoint R r
  assert |- ( ph -> ( _I |` U. U. R ) C_ ( C ` R ) )

  proof
    wph
    cid
    cR
    cuni
    cuni
    #
    cres
    cid
    cR
    cdm
    cR
    crn
    cun
    #
    cres
    cR
    cC
    cfv
    wph
    @0
    @1
    cid
    wph
    cR
    wrel
    @0
    @1
    wceq
    fvmptiunrelexplb0da.rel
    cR
    relfld
    syl
    reseq2d
    wph
    cC
    cR
    vn
    cN
    vr
    fvmptiunrelexplb0da.c
    fvmptiunrelexplb0da.r
    fvmptiunrelexplb0da.n
    fvmptiunrelexplb0da.0
    fvmptiunrelexplb0d
    eqsstrd
end

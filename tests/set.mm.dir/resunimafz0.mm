include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cima.mm"
include "cres.mm"
include "cfzo.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "cop.mm"
include "imaundi.mm"
include "cuz.mm"
include "wcel.mm"
include "wceq.mm"
include "cn0.mm"
include "chash.mm"
include "elfzonn0.mm"
include "syl.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzisfzounsn.mm"
include "imaeq2d.mm"
include "wfn.mm"
include "cdm.mm"
include "ffnd.mm"
include "fnsnfv.mm"
include "syl2anc.mm"
include "uneq2d.mm"
include "3eqtr4a.mm"
include "reseq2d.mm"
include "resundi.mm"
include "syl6eq.mm"
include "wfun.mm"
include "funfn.mm"
include "ffvelrnd.mm"
include "fnressn.mm"
include "eqtrd.mm"

theorem resunimafz0
  let wph: wff ph
  let cF: class F
  let cI: class I
  let cN: class N
  assume resunimafz0.i: |- ( ph -> Fun I )
  assume resunimafz0.f: |- ( ph -> F : ( 0 ..^ ( # ` F ) ) --> dom I )
  assume resunimafz0.n: |- ( ph -> N e. ( 0 ..^ ( # ` F ) ) )


  assert |- ( ph -> ( I |` ( F " ( 0 ... N ) ) ) = ( ( I |` ( F " ( 0 ..^ N ) ) ) u. { <. ( F ` N ) , ( I ` ( F ` N ) ) >. } ) )

  proof
    wph
    cI
    cF
    cc0
    cN
    cfz
    co
    #
    cima
    #
    cres
    #
    cI
    cF
    cc0
    cN
    cfzo
    co
    #
    cima
    #
    cres
    #
    cI
    cN
    cF
    cfv
    #
    csn
    #
    cres
    #
    cun
    #
    @5
    @6
    @6
    cI
    cfv
    cop
    csn
    #
    cun
    wph
    @2
    cI
    @4
    @7
    cun
    #
    cres
    @9
    wph
    @1
    @11
    cI
    wph
    cF
    @3
    cN
    csn
    #
    cun
    #
    cima
    @4
    cF
    @12
    cima
    #
    cun
    @1
    @11
    cF
    @3
    @12
    imaundi
    wph
    @0
    @13
    cF
    wph
    cN
    cc0
    cuz
    cfv
    wcel
    #
    @0
    @13
    wceq
    wph
    cN
    cn0
    wcel
    #
    @15
    wph
    cN
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    #
    @16
    resunimafz0.n
    cN
    @17
    elfzonn0
    syl
    cN
    elnn0uz
    sylib
    cc0
    cN
    fzisfzounsn
    syl
    imaeq2d
    wph
    @7
    @14
    @4
    wph
    cF
    @18
    wfn
    @19
    @7
    @14
    wceq
    wph
    @18
    cI
    cdm
    #
    cF
    resunimafz0.f
    ffnd
    resunimafz0.n
    @18
    cN
    cF
    fnsnfv
    syl2anc
    uneq2d
    3eqtr4a
    reseq2d
    cI
    @4
    @7
    resundi
    syl6eq
    wph
    @8
    @10
    @5
    wph
    cI
    @20
    wfn
    #
    @6
    @20
    wcel
    @8
    @10
    wceq
    wph
    cI
    wfun
    @21
    resunimafz0.i
    cI
    funfn
    sylib
    wph
    @18
    @20
    cN
    cF
    resunimafz0.f
    resunimafz0.n
    ffvelrnd
    @20
    @6
    cI
    fnressn
    syl2anc
    uneq2d
    eqtrd
end

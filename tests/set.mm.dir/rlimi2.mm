include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cpnf.mm"
include "cico.mm"
include "wrex.mm"
include "cr.mm"
include "rlimi.mm"
include "wss.mm"
include "wcel.mm"
include "wb.mm"
include "cmpt.mm"
include "cdm.mm"
include "wfn.mm"
include "wceq.mm"
include "eqid.mm"
include "fnmpt.mm"
include "fndm.mm"
include "3syl.mm"
include "crli.mm"
include "rlimss.mm"
include "syl.mm"
include "eqsstr3d.mm"
include "rexico.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem rlimi2
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cV: class V
  let vx: setvar x
  assume rlimi.1: |- ( ph -> A. z e. A B e. V )
  assume rlimi.2: |- ( ph -> R e. RR+ )
  assume rlimi.3: |- ( ph -> ( z e. A |-> B ) ~~>r C )
  assume rlimi.4: |- ( ph -> D e. RR )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint C y
  disjoint C z
  disjoint ph y
  disjoint R y
  disjoint R z
  disjoint D y
  disjoint D z
  disjoint V z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  disjoint R x
  assert |- ( ph -> E. y e. ( D [,) +oo ) A. z e. A ( y <_ z -> ( abs ` ( B - C ) ) < R ) )

  proof
    wph
    vy
    cv
    vz
    cv
    cle
    wbr
    cB
    cC
    cmin
    co
    cabs
    cfv
    cR
    clt
    wbr
    #
    wi
    vz
    cA
    wral
    #
    vy
    cD
    cpnf
    cico
    co
    wrex
    #
    @1
    vy
    cr
    wrex
    #
    wph
    vy
    vz
    cA
    cB
    cC
    cR
    cV
    rlimi.1
    rlimi.2
    rlimi.3
    rlimi
    wph
    cA
    cr
    wss
    cD
    cr
    wcel
    @2
    @3
    wb
    wph
    cA
    vz
    cA
    cB
    cmpt
    #
    cdm
    #
    cr
    wph
    cB
    cV
    wcel
    vz
    cA
    wral
    @4
    cA
    wfn
    @5
    cA
    wceq
    rlimi.1
    vz
    cA
    cB
    @4
    cV
    @4
    eqid
    fnmpt
    cA
    @4
    fndm
    3syl
    wph
    @4
    cC
    crli
    wbr
    @5
    cr
    wss
    rlimi.3
    cC
    @4
    rlimss
    syl
    eqsstr3d
    rlimi.4
    @0
    cA
    cD
    vy
    vz
    rexico
    syl2anc
    mpbird
end

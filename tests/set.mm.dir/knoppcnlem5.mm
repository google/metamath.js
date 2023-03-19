include "cn0.mm"
include "cr.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cn.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplr.mm"
include "knoppcnlem3.mm"
include "recnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "reex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem knoppcnlem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cN: class N
  assume knoppcnlem5.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcnlem5.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcnlem5.n: |- ( ph -> N e. NN )
  assume knoppcnlem5.1: |- ( ph -> C e. RR )

  disjoint C n
  disjoint C y
  disjoint n y
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint ph z
  disjoint m n
  disjoint m y
  disjoint m z
  disjoint n z
  disjoint y z
  disjoint m x
  disjoint x z
  assert |- ( ph -> ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) ) : NN0 --> ( CC ^m RR ) )

  proof
    wph
    vm
    cn0
    vz
    cr
    vm
    cv
    #
    vz
    cv
    #
    cF
    cfv
    cfv
    #
    cmpt
    #
    cc
    cr
    cmap
    co
    #
    vm
    cn0
    @3
    cmpt
    #
    wph
    @0
    cn0
    wcel
    #
    wa
    #
    cr
    cc
    @3
    wf
    #
    @3
    @4
    wcel
    #
    @7
    vz
    cr
    @2
    cc
    @3
    @7
    @1
    cr
    wcel
    #
    wa
    #
    @2
    @11
    vx
    vy
    @1
    cC
    cT
    vn
    cF
    @0
    cN
    knoppcnlem5.t
    knoppcnlem5.f
    wph
    cN
    cn
    wcel
    @6
    @10
    knoppcnlem5.n
    ad2antrr
    wph
    cC
    cr
    wcel
    @6
    @10
    knoppcnlem5.1
    ad2antrr
    @7
    @10
    simpr
    wph
    @6
    @10
    simplr
    knoppcnlem3
    recnd
    @3
    eqid
    fmptd
    cc
    cvv
    wcel
    #
    cr
    cvv
    wcel
    #
    wa
    @9
    @8
    wb
    @12
    @13
    cnex
    reex
    pm3.2i
    cc
    cr
    @3
    cvv
    cvv
    elmapg
    ax-mp
    sylibr
    @5
    eqid
    fmptd
end

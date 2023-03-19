include "cpi1.mm"
include "co.mm"
include "cphtpc.mm"
include "cfv.mm"
include "cqus.mm"
include "ctop.mm"
include "cv.mm"
include "cuni.mm"
include "comi.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-pi1.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "unieq.mm"
include "adantl.mm"
include "ctopon.mm"
include "wcel.mm"
include "toponuni.mm"
include "syl.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "topontop.mm"
include "ovexd.mm"
include "ovmpt2dx.mm"
include "syl5eq.mm"

theorem pi1val
  let wph: wff ph
  let cG: class G
  let cJ: class J
  let cO: class O
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  assume pi1val.g: |- G = ( J pi1 Y )
  assume pi1val.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1val.2: |- ( ph -> Y e. X )
  assume pi1val.o: |- O = ( J Om1 Y )


  assert |- ( ph -> G = ( O /s ( ~=ph ` J ) ) )

  proof
    wph
    cG
    cJ
    cY
    cpi1
    co
    cO
    cJ
    cphtpc
    cfv
    #
    cqus
    co
    #
    pi1val.g
    wph
    vj
    vy
    cJ
    cY
    ctop
    vj
    cv
    #
    cuni
    #
    @2
    vy
    cv
    #
    comi
    co
    #
    @2
    cphtpc
    cfv
    #
    cqus
    co
    #
    @1
    cpi1
    cX
    cvv
    cpi1
    vj
    vy
    ctop
    @3
    @7
    cmpt2
    wceq
    wph
    vy
    vj
    df-pi1
    a1i
    wph
    @2
    cJ
    wceq
    #
    @4
    cY
    wceq
    #
    wa
    wa
    #
    @5
    cO
    @6
    @0
    cqus
    @10
    @5
    cJ
    cY
    comi
    co
    cO
    @10
    @2
    cJ
    @4
    cY
    comi
    wph
    @8
    @9
    simprl
    #
    wph
    @8
    @9
    simprr
    oveq12d
    pi1val.o
    syl6eqr
    @10
    @2
    cJ
    cphtpc
    @11
    fveq2d
    oveq12d
    wph
    @8
    wa
    @3
    cJ
    cuni
    #
    cX
    @8
    @3
    @12
    wceq
    wph
    @2
    cJ
    unieq
    adantl
    wph
    cX
    @12
    wceq
    #
    @8
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @13
    pi1val.1
    cX
    cJ
    toponuni
    syl
    adantr
    eqtr4d
    wph
    @14
    cJ
    ctop
    wcel
    pi1val.1
    cX
    cJ
    topontop
    syl
    pi1val.2
    wph
    cO
    @0
    cqus
    ovexd
    ovmpt2dx
    syl5eq
end

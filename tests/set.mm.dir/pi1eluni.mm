include "cuni.mm"
include "comi.mm"
include "co.mm"
include "eqid.mm"
include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "pi1buni.mm"
include "om1elbas.mm"

theorem pi1eluni
  let wph: wff ph
  let cB: class B
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cO: class O
  assume pi1val.g: |- G = ( J pi1 Y )
  assume pi1val.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1val.2: |- ( ph -> Y e. X )
  assume pi1bas2.b: |- ( ph -> B = ( Base ` G ) )


  assert |- ( ph -> ( F e. U. B <-> ( F e. ( II Cn J ) /\ ( F ` 0 ) = Y /\ ( F ` 1 ) = Y ) ) )

  proof
    wph
    cB
    cuni
    cF
    cJ
    cJ
    cY
    comi
    co
    #
    cX
    cY
    @0
    eqid
    #
    pi1val.1
    pi1val.2
    wph
    cB
    cG
    cJ
    @0
    cbs
    cfv
    #
    @0
    cX
    cY
    pi1val.g
    pi1val.1
    pi1val.2
    @1
    pi1bas2.b
    wph
    @2
    eqidd
    pi1buni
    om1elbas
end

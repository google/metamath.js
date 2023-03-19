include "cuni.mm"
include "comi.mm"
include "co.mm"
include "eqid.mm"
include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "pi1buni.mm"
include "pi1bas.mm"

theorem pi1bas2
  let wph: wff ph
  let cB: class B
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


  assert |- ( ph -> B = ( U. B /. ( ~=ph ` J ) ) )

  proof
    wph
    cB
    cG
    cJ
    cB
    cuni
    cJ
    cY
    comi
    co
    #
    cX
    cY
    pi1val.g
    pi1val.1
    pi1val.2
    @0
    eqid
    #
    pi1bas2.b
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
    pi1bas
end

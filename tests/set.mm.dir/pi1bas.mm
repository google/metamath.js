include "cbs.mm"
include "cfv.mm"
include "cphtpc.mm"
include "cqs.mm"
include "cvv.mm"
include "pi1val.mm"
include "eqidd.mm"
include "fvexd.mm"
include "wcel.mm"
include "comi.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "qusbas.mm"
include "wceq.mm"
include "qseq1.mm"
include "syl.mm"
include "3eqtr4rd.mm"

theorem pi1bas
  let wph: wff ph
  let cB: class B
  let cG: class G
  let cJ: class J
  let cK: class K
  let cO: class O
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume pi1val.g: |- G = ( J pi1 Y )
  assume pi1val.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1val.2: |- ( ph -> Y e. X )
  assume pi1val.o: |- O = ( J Om1 Y )
  assume pi1bas.b: |- ( ph -> B = ( Base ` G ) )
  assume pi1bas.k: |- ( ph -> K = ( Base ` O ) )


  assert |- ( ph -> B = ( K /. ( ~=ph ` J ) ) )

  proof
    wph
    cO
    cbs
    cfv
    #
    cJ
    cphtpc
    cfv
    #
    cqs
    #
    cG
    cbs
    cfv
    cK
    @1
    cqs
    #
    cB
    wph
    @1
    cO
    cG
    @0
    cvv
    cvv
    wph
    cG
    cJ
    cO
    cX
    cY
    pi1val.g
    pi1val.1
    pi1val.2
    pi1val.o
    pi1val
    wph
    @0
    eqidd
    wph
    cJ
    cphtpc
    fvexd
    cO
    cvv
    wcel
    wph
    cO
    cJ
    cY
    comi
    co
    cvv
    pi1val.o
    cJ
    cY
    comi
    ovex
    eqeltri
    a1i
    qusbas
    wph
    cK
    @0
    wceq
    @3
    @2
    wceq
    pi1bas.k
    cK
    @0
    @1
    qseq1
    syl
    pi1bas.b
    3eqtr4rd
end

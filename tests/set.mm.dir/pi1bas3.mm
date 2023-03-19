include "cuni.mm"
include "cphtpc.mm"
include "cfv.mm"
include "cxp.mm"
include "cin.mm"
include "cqs.mm"
include "pi1bas2.mm"
include "cima.mm"
include "wss.mm"
include "wceq.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "comi.mm"
include "eqid.mm"
include "cbs.mm"
include "eqidd.mm"
include "pi1buni.mm"
include "pi1blem.mm"
include "simpld.mm"
include "qsinxp.mm"
include "syl.mm"
include "eqtrd.mm"
include "qseq2.mm"
include "ax-mp.mm"
include "syl6eqr.mm"

theorem pi1bas3
  let wph: wff ph
  let cB: class B
  let cR: class R
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
  assume pi1bas3.r: |- R = ( ( ~=ph ` J ) i^i ( U. B X. U. B ) )


  assert |- ( ph -> B = ( U. B /. R ) )

  proof
    wph
    cB
    cB
    cuni
    #
    cJ
    cphtpc
    cfv
    #
    @0
    @0
    cxp
    cin
    #
    cqs
    #
    @0
    cR
    cqs
    #
    wph
    cB
    @0
    @1
    cqs
    #
    @3
    wph
    cB
    cG
    cJ
    cX
    cY
    pi1val.g
    pi1val.1
    pi1val.2
    pi1bas2.b
    pi1bas2
    wph
    @1
    @0
    cima
    @0
    wss
    #
    @5
    @3
    wceq
    wph
    @6
    @0
    cii
    cJ
    ccn
    co
    wss
    wph
    cB
    cG
    cJ
    @0
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
    @7
    eqid
    #
    pi1bas2.b
    wph
    cB
    cG
    cJ
    @7
    cbs
    cfv
    #
    @7
    cX
    cY
    pi1val.g
    pi1val.1
    pi1val.2
    @8
    pi1bas2.b
    wph
    @9
    eqidd
    pi1buni
    pi1blem
    simpld
    @0
    @1
    qsinxp
    syl
    eqtrd
    cR
    @2
    wceq
    @4
    @3
    wceq
    pi1bas3.r
    cR
    @2
    @0
    qseq2
    ax-mp
    syl6eqr
end

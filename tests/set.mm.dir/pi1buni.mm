include "cuni.mm"
include "cphtpc.mm"
include "cfv.mm"
include "cxp.mm"
include "cin.mm"
include "cqs.mm"
include "pi1bas.mm"
include "cima.mm"
include "wss.mm"
include "wceq.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "pi1blem.mm"
include "simpld.mm"
include "qsinxp.mm"
include "syl.mm"
include "eqtrd.mm"
include "unieqd.mm"
include "cvv.mm"
include "wer.mm"
include "phtpcer.mm"
include "a1i.mm"
include "simprd.mm"
include "erinxp.mm"
include "wcel.mm"
include "fvex.mm"
include "inex1.mm"
include "uniqs2.mm"

theorem pi1buni
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


  assert |- ( ph -> U. B = K )

  proof
    wph
    cB
    cuni
    cK
    cJ
    cphtpc
    cfv
    #
    cK
    cK
    cxp
    #
    cin
    #
    cqs
    #
    cuni
    cK
    wph
    cB
    @3
    wph
    cB
    cK
    @0
    cqs
    #
    @3
    wph
    cB
    cG
    cJ
    cK
    cO
    cX
    cY
    pi1val.g
    pi1val.1
    pi1val.2
    pi1val.o
    pi1bas.b
    pi1bas.k
    pi1bas
    wph
    @0
    cK
    cima
    cK
    wss
    #
    @4
    @3
    wceq
    wph
    @5
    cK
    cii
    cJ
    ccn
    co
    #
    wss
    #
    wph
    cB
    cG
    cJ
    cK
    cO
    cX
    cY
    pi1val.g
    pi1val.1
    pi1val.2
    pi1val.o
    pi1bas.b
    pi1bas.k
    pi1blem
    #
    simpld
    cK
    @0
    qsinxp
    syl
    eqtrd
    unieqd
    wph
    cK
    @2
    cvv
    wph
    @6
    cK
    @0
    @6
    @0
    wer
    wph
    cJ
    phtpcer
    a1i
    wph
    @5
    @7
    @8
    simprd
    erinxp
    @2
    cvv
    wcel
    wph
    @0
    @1
    cJ
    cphtpc
    fvex
    inex1
    a1i
    uniqs2
    eqtrd
end

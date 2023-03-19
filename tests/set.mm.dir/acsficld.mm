include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cima.mm"
include "cuni.mm"
include "wceq.mm"
include "acsficl.mm"
include "syl2anc.mm"

theorem acsficld
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cN: class N
  let cX: class X
  assume acsficld.1: |- ( ph -> A e. ( ACS ` X ) )
  assume acsficld.2: |- N = ( mrCls ` A )
  assume acsficld.3: |- ( ph -> S C_ X )


  assert |- ( ph -> ( N ` S ) = U. ( N " ( ~P S i^i Fin ) ) )

  proof
    wph
    cA
    cX
    cacs
    cfv
    wcel
    cS
    cX
    wss
    cS
    cN
    cfv
    cN
    cS
    cpw
    cfn
    cin
    cima
    cuni
    wceq
    acsficld.1
    acsficld.3
    cA
    cS
    cN
    cX
    acsficld.2
    acsficl
    syl2anc
end

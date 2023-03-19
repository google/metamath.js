include "cioo.mm"
include "co.mm"
include "eqid.mm"
include "ioonct.mm"
include "wss.mm"
include "cioc.mm"
include "ioossioc.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "ssnct.mm"

theorem iocnct
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume iocnct.a: |- ( ph -> A e. RR* )
  assume iocnct.b: |- ( ph -> B e. RR* )
  assume iocnct.l: |- ( ph -> A < B )
  assume iocnct.c: |- C = ( A (,] B )


  assert |- ( ph -> -. C ~<_ _om )

  proof
    wph
    cA
    cB
    cioo
    co
    #
    cC
    wph
    cA
    cB
    @0
    iocnct.a
    iocnct.b
    iocnct.l
    @0
    eqid
    ioonct
    @0
    cC
    wss
    wph
    @0
    cA
    cB
    cioc
    co
    cC
    cA
    cB
    ioossioc
    iocnct.c
    sseqtr4i
    a1i
    ssnct
end

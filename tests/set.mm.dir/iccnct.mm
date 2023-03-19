include "cioo.mm"
include "co.mm"
include "eqid.mm"
include "ioonct.mm"
include "wss.mm"
include "cicc.mm"
include "ioossicc.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "ssnct.mm"

theorem iccnct
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume iccnct.a: |- ( ph -> A e. RR* )
  assume iccnct.b: |- ( ph -> B e. RR* )
  assume iccnct.l: |- ( ph -> A < B )
  assume iccnct.c: |- C = ( A [,] B )


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
    iccnct.a
    iccnct.b
    iccnct.l
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
    cicc
    co
    cC
    cA
    cB
    ioossicc
    iccnct.c
    sseqtr4i
    a1i
    ssnct
end

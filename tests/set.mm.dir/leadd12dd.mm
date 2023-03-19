include "caddc.mm"
include "co.mm"
include "readdcld.mm"
include "leadd1dd.mm"
include "leadd2dd.mm"
include "letrd.mm"

theorem leadd12dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume leadd12dd.a: |- ( ph -> A e. RR )
  assume leadd12dd.b: |- ( ph -> B e. RR )
  assume leadd12dd.c: |- ( ph -> C e. RR )
  assume leadd12dd.d: |- ( ph -> D e. RR )
  assume leadd12dd.ac: |- ( ph -> A <_ C )
  assume leadd12dd.bd: |- ( ph -> B <_ D )


  assert |- ( ph -> ( A + B ) <_ ( C + D ) )

  proof
    wph
    cA
    cB
    caddc
    co
    cC
    cB
    caddc
    co
    cC
    cD
    caddc
    co
    wph
    cA
    cB
    leadd12dd.a
    leadd12dd.b
    readdcld
    wph
    cC
    cB
    leadd12dd.c
    leadd12dd.b
    readdcld
    wph
    cC
    cD
    leadd12dd.c
    leadd12dd.d
    readdcld
    wph
    cA
    cC
    cB
    leadd12dd.a
    leadd12dd.c
    leadd12dd.b
    leadd12dd.ac
    leadd1dd
    wph
    cB
    cD
    cC
    leadd12dd.b
    leadd12dd.d
    leadd12dd.c
    leadd12dd.bd
    leadd2dd
    letrd
end

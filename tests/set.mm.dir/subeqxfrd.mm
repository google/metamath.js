include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "oveq1d.mm"
include "npncand.mm"
include "npncan3d.mm"
include "3eqtr3d.mm"

theorem subeqxfrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume subeqxfrd.a: |- ( ph -> A e. CC )
  assume subeqxfrd.b: |- ( ph -> B e. CC )
  assume subeqxfrd.c: |- ( ph -> C e. CC )
  assume subeqxfrd.d: |- ( ph -> D e. CC )
  assume subeqxfrd.1: |- ( ph -> ( A - B ) = ( C - D ) )


  assert |- ( ph -> ( A - C ) = ( B - D ) )

  proof
    wph
    cA
    cB
    cmin
    co
    #
    cB
    cC
    cmin
    co
    #
    caddc
    co
    cC
    cD
    cmin
    co
    #
    @1
    caddc
    co
    cA
    cC
    cmin
    co
    cB
    cD
    cmin
    co
    wph
    @0
    @2
    @1
    caddc
    subeqxfrd.1
    oveq1d
    wph
    cA
    cB
    cC
    subeqxfrd.a
    subeqxfrd.b
    subeqxfrd.c
    npncand
    wph
    cC
    cD
    cB
    subeqxfrd.c
    subeqxfrd.d
    subeqxfrd.b
    npncan3d
    3eqtr3d
end

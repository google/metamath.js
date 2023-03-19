include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmo.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "zcnd.mm"
include "sqvald.mm"
include "oveq1d.mm"
include "cz.mm"
include "wcel.mm"
include "neg1z.mm"
include "a1i.mm"
include "modmul12d.mm"
include "eqtrd.mm"
include "wceq.mm"
include "neg1mulneg1e1.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "rpred.mm"
include "1mod.mm"
include "syl2anc.mm"

theorem modexp2m1d
  let wph: wff ph
  let cA: class A
  let cE: class E
  let vk: setvar k
  let vx: setvar x
  assume modexp2m1d.a: |- ( ph -> A e. ZZ )
  assume modexp2m1d.e: |- ( ph -> E e. RR+ )
  assume modexp2m1d.g: |- ( ph -> 1 < E )
  assume modexp2m1d.m: |- ( ph -> ( A mod E ) = ( -u 1 mod E ) )


  assert |- ( ph -> ( ( A ^ 2 ) mod E ) = 1 )

  proof
    wph
    cA
    c2
    cexp
    co
    #
    cE
    cmo
    co
    #
    c1
    cneg
    #
    @2
    cmul
    co
    #
    cE
    cmo
    co
    #
    c1
    wph
    @1
    cA
    cA
    cmul
    co
    #
    cE
    cmo
    co
    @4
    wph
    @0
    @5
    cE
    cmo
    wph
    cA
    wph
    cA
    modexp2m1d.a
    zcnd
    sqvald
    oveq1d
    wph
    cA
    @2
    cA
    @2
    cE
    modexp2m1d.a
    @2
    cz
    wcel
    wph
    neg1z
    a1i
    #
    modexp2m1d.a
    @6
    modexp2m1d.e
    modexp2m1d.m
    modexp2m1d.m
    modmul12d
    eqtrd
    wph
    @4
    c1
    cE
    cmo
    co
    #
    c1
    wph
    @3
    c1
    cE
    cmo
    @3
    c1
    wceq
    wph
    neg1mulneg1e1
    a1i
    oveq1d
    wph
    cE
    cr
    wcel
    c1
    cE
    clt
    wbr
    @7
    c1
    wceq
    wph
    cE
    modexp2m1d.e
    rpred
    modexp2m1d.g
    cE
    1mod
    syl2anc
    eqtrd
    eqtrd
end

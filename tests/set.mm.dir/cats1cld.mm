include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cword.mm"
include "wcel.mm"
include "s1cld.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"

theorem cats1cld
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cX: class X
  assume cats1cld.1: |- T = ( S ++ <" X "> )
  assume cats1cld.2: |- ( ph -> S e. Word A )
  assume cats1cld.3: |- ( ph -> X e. A )


  assert |- ( ph -> T e. Word A )

  proof
    wph
    cT
    cS
    cX
    cs1
    #
    cconcat
    co
    #
    cA
    cword
    #
    cats1cld.1
    wph
    cS
    @2
    wcel
    @0
    @2
    wcel
    @1
    @2
    wcel
    cats1cld.2
    wph
    cX
    cA
    cats1cld.3
    s1cld
    cA
    cS
    @0
    ccatcl
    syl2anc
    syl5eqel
end

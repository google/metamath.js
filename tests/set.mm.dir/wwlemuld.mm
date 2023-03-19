include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "elrpd.mm"
include "lemul2d.mm"
include "mpbird.mm"

theorem wwlemuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume wwlemuld.1: |- ( ph -> A e. RR )
  assume wwlemuld.2: |- ( ph -> B e. RR )
  assume wwlemuld.3: |- ( ph -> C e. RR )
  assume wwlemuld.4: |- ( ph -> ( C x. A ) <_ ( C x. B ) )
  assume wwlemuld.5: |- ( ph -> 0 < C )


  assert |- ( ph -> A <_ B )

  proof
    wph
    cA
    cB
    cle
    wbr
    cC
    cA
    cmul
    co
    cC
    cB
    cmul
    co
    cle
    wbr
    wwlemuld.4
    wph
    cA
    cB
    cC
    wwlemuld.1
    wwlemuld.2
    wph
    cC
    wwlemuld.3
    wwlemuld.5
    elrpd
    lemul2d
    mpbird
end

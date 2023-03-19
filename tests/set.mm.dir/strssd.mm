include "cfv.mm"
include "cnx.mm"
include "cop.mm"
include "sseldd.mm"
include "strfvd.mm"
include "cvv.mm"
include "ssexd.mm"
include "wss.mm"
include "wfun.mm"
include "funss.mm"
include "sylc.mm"
include "eqtr3d.mm"

theorem strssd
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cT: class T
  let cE: class E
  let cV: class V
  assume strssd.e: |- E = Slot ( E ` ndx )
  assume strssd.t: |- ( ph -> T e. V )
  assume strssd.f: |- ( ph -> Fun T )
  assume strssd.s: |- ( ph -> S C_ T )
  assume strssd.n: |- ( ph -> <. ( E ` ndx ) , C >. e. S )


  assert |- ( ph -> ( E ` T ) = ( E ` S ) )

  proof
    wph
    cC
    cT
    cE
    cfv
    cS
    cE
    cfv
    wph
    cC
    cT
    cE
    cV
    strssd.e
    strssd.t
    strssd.f
    wph
    cS
    cT
    cnx
    cE
    cfv
    cC
    cop
    strssd.s
    strssd.n
    sseldd
    strfvd
    wph
    cC
    cS
    cE
    cvv
    strssd.e
    wph
    cS
    cT
    cV
    strssd.t
    strssd.s
    ssexd
    wph
    cS
    cT
    wss
    cT
    wfun
    cS
    wfun
    strssd.s
    strssd.f
    cS
    cT
    funss
    sylc
    strssd.n
    strfvd
    eqtr3d
end

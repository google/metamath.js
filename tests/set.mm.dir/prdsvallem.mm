include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cip.mm"
include "cun.mm"
include "cts.mm"
include "cple.mm"
include "cds.mm"
include "chom.mm"
include "cco.mm"
include "cpr.mm"
include "cvv.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "prdsvalstr.mm"
include "strfv3.mm"

theorem prdsvallem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let c.xb: class .xb
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cH: class H
  let c.xi: class .,
  let cL: class L
  let cO: class O
  assume prdsvallem.u: |- ( ph -> U = ( ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , ., >. } ) u. ( { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , L >. , <. ( dist ` ndx ) , D >. } u. { <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .xb >. } ) ) )
  assume prdsvallem.1: |- A = ( E ` U )
  assume prdsvallem.2: |- E = Slot ( E ` ndx )
  assume prdsvallem.3: |- ( ph -> T e. _V )
  assume prdsvallem.4: |- { <. ( E ` ndx ) , T >. } C_ ( ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , ., >. } ) u. ( { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , L >. , <. ( dist ` ndx ) , D >. } u. { <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .xb >. } ) )


  assert |- ( ph -> A = T )

  proof
    wph
    cA
    cT
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    cplusg
    cfv
    c.pl
    cop
    cnx
    cmulr
    cfv
    c.xp
    cop
    ctp
    cnx
    csca
    cfv
    cS
    cop
    cnx
    cvsca
    cfv
    c.x
    cop
    cnx
    cip
    cfv
    c.xi
    cop
    ctp
    cun
    cnx
    cts
    cfv
    cO
    cop
    cnx
    cple
    cfv
    cL
    cop
    cnx
    cds
    cfv
    cD
    cop
    ctp
    cnx
    chom
    cfv
    cH
    cop
    cnx
    cco
    cfv
    c.xb
    cop
    cpr
    cun
    cun
    cU
    cE
    cvv
    c1
    c1
    c5
    cdc
    cop
    prdsvallem.u
    cB
    cD
    c.pl
    cS
    c.xb
    c.x
    c.xp
    cH
    c.xi
    cL
    cO
    prdsvalstr
    prdsvallem.2
    prdsvallem.4
    prdsvallem.3
    prdsvallem.1
    strfv3
end

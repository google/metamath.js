const {descent: {parse, process}, metamath: {MM}} = module;

class Code extends React.Component {
  render() {
    const c = this.props.mm.labels["$c"].map(([, c]) => c).flat();
    
    return (
      <code style={{padding: "0.3em 0.5em"}}>
        {this.props.src.split(" ").map((ch, i) =>
          c.includes(ch) ?
            <b style={{color: "#7928a1", padding: "0.2em", cursor: "pointer"}} title={`${ch} is a declared constant.`} key={i}>{ch}</b> :
            <span key={i} style={{color: "#d91e18", padding: "0.2em", cursor: "pointer"}} title={`${ch} is a declared var.`}>{ch}</span>)}
      </code>
    );
  }
}

class Theorem extends React.Component {
  render() {
    const mm = this.props.mm;
    const statement = mm.labels[this.props.label];
    let [a, [d = [], args = [], hyp = [], [type = "", theorem = []] = []], proof = () => []] = statement;

    return (
      <div>
        {false &&
         <h1>{a == "$a" ? "Axiom" : "Theorem"} "{this.props.label}"</h1>
        }

         {!statement && (
            <div>
              <img src="/static/loading.gif"></img>
            </div>
         )}
      
         {theorem.length > 0 && (
            <div>
             <h2>Assertion</h2>
             <table>
               <thead>
                 <tr><th>Type</th><th>Assertion</th></tr>
               </thead>
               <tbody>
               <tr>
                 <td><Code mm={mm} src={type}/></td><td><Code mm={mm} src={theorem.join(" ")}/></td>
               </tr>
               </tbody>
             </table>
           </div>
         )}

         {hyp.length > 0 && (
           <div>
             <h2>Assumptions</h2>  
             <table>
               <thead>
                <tr><th>Label</th><th>Type</th><th>Condition</th></tr>
                </thead>
               <tbody>
               {hyp.map(([sequence, type, label], i) =>
                 <tr key={i}>
                   <td>{label}</td><td><Code mm={mm} src={type}/></td><td><Code mm={mm} src={sequence.join(" ")}/></td>
                 </tr>
               )}
               </tbody>
             </table>
           </div>
         )}

         {false && args.length > 0 && (
           <div>     
             <h2>Arguments</h2>  
             <table>
               <thead>
                 <tr><th>Label</th><th>Type</th><th>Symbol</th></tr>
               </thead>
               <tbody>
               {args.map(([type, name, label], i) =>
               <tr key={i}>
                   <td>{label}</td>
                   <td><Code mm={mm} src={type}/></td>
                   <td><Code mm={mm} src={name}/></td>
               </tr>
               )}
               </tbody>
             </table>
           </div>
         )}

         {a == "$p" && 
           <Proof mm={mm} proof={proof()}/>
         }

        </div>
    );
  }
}

class Window extends React.Component {
  render() {

    if (!this.props.open) {
      return null;
    }
    
    const mm = this.props.mm;

    if (!mm.labels[this.props.open]) {
      return null;
    }
    
    //const open = this.props.open ? this.props.mm.labels[this.props.open] : undefined;
    const open = mm.labels[this.props.open];
    const style = {
      position: "absolute",
      left: "105%",
      width: "80%",
      borderRadius: "6px",
      padding: "0 1em",
      boxShadow:  "0 0 10px rgba(0,0,0,0.3)",
      paddingBottom: "2em",
      bottom: 0,
      overflow: "scroll"
    };
    return (
        <div style={style}>
          {open[0] == "$f" && (
            <React.Fragment>    
              <h1>
                Type Declaration "{this.props.open}"
              </h1>
              <table>
                <thead>
                  <tr><th>Type</th><th>Name</th></tr>
                </thead>
                <tbody>
                  <tr>
                    <td><Code mm={mm} src={open[1][0]} /></td><td><Code mm={mm} src={open[1][1]}/></td>
                  </tr>
                </tbody>
              </table>
            </React.Fragment>
          )}

          {open[0] == "$e" && (
            <React.Fragment>    
              <h1>
                Assumption "{this.props.open}"
              </h1>
              <table>
                <thead>
                  <tr><th>Type</th><th>Name</th></tr>
                </thead>
                <tbody>
                  <tr>
                    <td><Code mm={mm} src={open[1][0]}/></td><td><Code mm={mm} src={open[1][1].join(" ")}/></td>
                  </tr>
                </tbody>
              </table>
            </React.Fragment>  
          )}

          {(open[0] == "$a" || open[0] == "$p") && (
            <Theorem mm={mm} label={this.props.open}></Theorem>
          )}

        </div>
    );
  }
}

class Proof extends React.Component {
  constructor(props) {
    super(props);
    this.state = {};
  }
  render() {
    if (!this.props.proof) {
      return null;
    }
    const mm = this.props.mm;
    const proof = this.props.proof;

    // console.log(proof);
    
    const style = function (highlight, i, type) {
      const base = type == "|-" ? {} : {display: "none"};
      if (!highlight) {
        return base;
      }
      if (highlight.includes(i)) {
        return base;
      }
      return Object.assign(base, {
        opacity: 0.1,
        backgroundColor: "none"
      });
    };
    
    return (
      <div>

        <h2>Proof</h2>

        <div style={{position: "relative", display: "inline-block"}}>
          <table>
            <thead>
              <tr><th>Step</th><th>Rule</th><th>Arguments</th><th>Type</th><th>Expression</th></tr>
            </thead>
            <tbody>
            {proof.map((step, i) => {
              const [label, rule = [], args = []] = step;
              // console.log(label);
              const [type = "", result = []] = rule;
              if (typeof label == "number") {
                return
                  <tr key={i}>
                    <td>${label}</td>
                    <td><Code mm={mm} src={type}/></td>
                    <td><Code mm={mm} src={result.flat().join(" ")}/></td>
                  </tr>
              }
              return (
              <tr key={i}
                style={style(this.state.highlight, i, type)}
                onMouseEnter={() => this.setState({"highlight": [...args, i], "open": label})}
                onMouseLeave={() => this.setState({"highlight": undefined, "open": undefined})}>
                <td>{i}</td>
                <td>{(mm.labels[label][0] == "$a" || mm.labels[label][0] == "$p") && (
                  <a href={"#" + label} onClick={() => {this.setState({"label": step});}}>{label}</a>
                )}
                {(mm.labels[label][0] != "$a" && mm.labels[label][0] != "$p") && (
                  step
                )}
                </td>
                <td>{args.join(", ")}</td>
                <td><Code mm={mm} src={type}/></td>
                <td><Code mm={mm} src={result.flat().join(" ")}/></td>
              </tr>
              )
              })
            }
            </tbody>
          </table>
          {false &&          
           <Window mm={mm} open={this.state.open}/>
          }
          </div>
        </div>
    );
  }
}

class Metamath extends React.Component {
  constructor(props) {
    super(props);
    const source = this.props.children;
    const label = window.location.hash ? window.location.hash.substr(1) : this.props.label;

    this.state = {
      label: label,
      file: this.props.file,
      open: false,
    };
  }

  async compute() {
    const label = window.location.hash ? window.location.hash.substr(1) : this.props.label;

    console.log(`Recomputing ${label}`);
    
    //this.setState({
    //});

    const compiler = new Compiler(this.loader.bind(this));

    const source = await compiler.compile(
      this.props.dir, `${label}.mm`, true);

    //console.log(this.props.file);
    
    const mm = process(source);
    
    //console.log(`Loaded ${source}`);
    // console.log();
    // const [, , verifier] = mm.labels[label];

    //console.log(mm.labels["eqtri"]);
    //verifier();

    this.setState({
      label: label,
      open: false,
      source: source,
      mm: process(source),
    });

    window.scroll({
      top: 0, 
      left: 0, 
      behavior: 'smooth' 
    });
  }
  
  async componentDidMount() {
    window.addEventListener('hashchange', this.compute.bind(this), false);
    // console.log(this.props.label);
    this.compute();
  }

  async loader(file) {
    const response = await fetch(file);
    const body = await response.text();
    
    // resolve(body);
    // return body;

    const that = this;
    return new Promise((resolve, reject) => {
      // Waits 100 ms arbitrarily to simulate slow
      // networks
      // console.log(`Loading ${file}`);
      // console.log(that);
      that.setState({
        file: file
      });
      setTimeout(() => {
        resolve(body);
      }, 0);
    });
    
    // return body;
  }  

  render() {

    if (!this.state.mm) {
      return (
      <div className="doc">
        <div className="post">
          <div className="post-title">
          <h1>Loading {this.state.label}</h1>
          </div>
          <div className="post-info">
            <div>metamath</div>
            <div className="post-date">2023</div>
          </div>
          <div className="post-body">
            Loading {this.state.file}
          </div>
        </div>
      </div>
      );
    }
    
    const statement = this.state.mm.labels[this.state.label];
    // let [a, [d = [], args = [], hyp = [], [type, theorem] = []], proof = () => []] = statement;
    const [a] = statement;

    const hash = window.location.hash;
    const mm = this.state.mm;
    
    return (
      <div className="doc">
        <div className="post">
          <div className="post-title">
          <h1>{a == "$p" ? "Theorem" : "Axiom"} {this.state.label}</h1>
          </div>
          <div className="post-info">
            <div>metamath</div>
            <div className="post-date">2023</div>
          </div>
          <div className="post-body">
            <Theorem mm={mm} label={this.state.label} />
          </div>
        </div>
      </div>
    );
  }
}

const {compiler: {Compiler}, descent: {Verifier}} = module;

class MetaMath extends HTMLElement {
  // connect component
  async connectedCallback() {

    const dir = this.getAttribute("dir");
    const file = this.getAttribute("file");
    const label = this.getAttribute("label");

    ReactDOM.render(
        <Metamath dir={dir} file={file} label={label}></Metamath>,
      this);
  }
}

customElements.define("meta-math", MetaMath);
